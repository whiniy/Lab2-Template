from model import (
    Location,
    Wizard,
    IceStone,
    FireStone,
    WizardMoves,
    GameAction,
    GameState,
    WizardSpells, NeutralStone,
)
from agents import WizardAgent

import z3
from z3 import (Solver, Bool, Bools, Int, Ints, Or, Not, And, Implies, Distinct, If)



class PuzzleWizard(WizardAgent):

    def react(self, state: GameState) -> WizardMoves:
        if hasattr(self, "finished") and self.finished:
            raise Exception("Puzzle already solved; no more moves needed.")

        if hasattr(self, "plan") and len(self.plan) > 0:
            move = self.plan.pop(0)
            if len(self.plan) == 0:
                self.finished = True
            return move

        fire_stones = state.get_all_tile_locations(FireStone)
        ice_stones = state.get_all_tile_locations(IceStone)

        # ── FIX 1 ──────────────────────────────────────────────────────────────
        # Collect ALL stone locations regardless of type so none are skipped.
        # Fire and ice stones get type-specific constraints below; any other
        # stone type just needs to be on the path (numEdges == 2).
        all_stone_locations = set()
        for stone in fire_stones:
            all_stone_locations.add((stone.row, stone.col))
        for stone in ice_stones:
            all_stone_locations.add((stone.row, stone.col))

        # Also pull in any neutral / unknown stone types via the base class so
        # that Medium-style puzzles (where some stones are neither fire nor ice)
        # are still forced onto the path.
        try:
            other_stones = state.get_all_tile_locations(Stone)
            for stone in other_stones:
                all_stone_locations.add((stone.row, stone.col))
        except Exception:
            pass  # Stone base-class may not exist in all environments

        grid_size = state.grid_size
        if isinstance(grid_size, tuple):
            rows, cols = grid_size
        else:
            rows = grid_size
            cols = grid_size

        wizard_location = state.active_entity_location
        start = (wizard_location.row, wizard_location.col)

        s = Solver()

        horizontalEdges = {}
        verticalEdges = {}

        for row in range(rows):
            for col in range(cols):
                if col < cols - 1:
                    horizontalEdges[(row, col)] = Bool(f"h{row}_{col}")
                if row < rows - 1:
                    verticalEdges[(row, col)] = Bool(f"v{row}_{col}")

        def isTouching(r, c):
            edges = []
            if (r, c - 1) in horizontalEdges:
                edges.append(horizontalEdges[(r, c - 1)])
            if (r, c) in horizontalEdges:
                edges.append(horizontalEdges[(r, c)])
            if (r - 1, c) in verticalEdges:
                edges.append(verticalEdges[(r - 1, c)])
            if (r, c) in verticalEdges:
                edges.append(verticalEdges[(r, c)])
            return edges

        def numEdges(edges):
            return sum([If(edge, 1, 0) for edge in edges])

        def directionalEdges(r, c):
            left  = horizontalEdges.get((r, c - 1), z3.BoolVal(False))
            right = horizontalEdges.get((r, c),     z3.BoolVal(False))
            up    = verticalEdges.get((r - 1, c),   z3.BoolVal(False))
            down  = verticalEdges.get((r, c),       z3.BoolVal(False))
            return left, right, up, down

        def isStraight(r, c):
            left, right, up, down = directionalEdges(r, c)
            return Or(And(left, right), And(up, down))

        def isTurn(r, c):
            left, right, up, down = directionalEdges(r, c)
            return Or(
                And(left, up),
                And(left, down),
                And(right, up),
                And(right, down),
            )

        # Every cell: 0 edges (off path) or 2 edges (on path)
        for row in range(rows):
            for col in range(cols):
                edges = isTouching(row, col)
                n = numEdges(edges)
                s.add(Or(n == 0, n == 2))

        # Wizard start must be on the path
        s.add(numEdges(isTouching(start[0], start[1])) == 2)

        # ── FIX 1 (continued) ──────────────────────────────────────────────────
        # Every stone (of any type) must be on the path
        for (r, c) in all_stone_locations:
            s.add(numEdges(isTouching(r, c)) == 2)

        # Fire stone type-specific constraints
        for stone in fire_stones:
            r, c = stone.row, stone.col
            left, right, up, down = directionalEdges(r, c)

            s.add(isTurn(r, c))

            s.add(Implies(And(left, up),
                And(isStraight(r, c - 1), isStraight(r - 1, c))))
            s.add(Implies(And(left, down),
                And(isStraight(r, c - 1), isStraight(r + 1, c))))
            s.add(Implies(And(right, up),
                And(isStraight(r, c + 1), isStraight(r - 1, c))))
            s.add(Implies(And(right, down),
                And(isStraight(r, c + 1), isStraight(r + 1, c))))

        # Ice stone type-specific constraints
        for stone in ice_stones:
            r, c = stone.row, stone.col
            left, right, up, down = directionalEdges(r, c)

            s.add(isStraight(r, c))

            s.add(Implies(And(left, right),
                Or(isTurn(r, c - 1), isTurn(r, c + 1))))
            s.add(Implies(And(up, down),
                Or(isTurn(r - 1, c), isTurn(r + 1, c))))

        # Solve, rejecting disconnected multi-loop solutions
        while True:
            if s.check() != z3.sat:
                raise Exception("No solution found for this Masyu puzzle.")

            model = s.model()
            adjacency = {}

            def addConn(a, b):
                adjacency.setdefault(a, []).append(b)
                adjacency.setdefault(b, []).append(a)

            for (r, c), edge in horizontalEdges.items():
                if z3.is_true(model.eval(edge, model_completion=True)):
                    addConn((r, c), (r, c + 1))

            for (r, c), edge in verticalEdges.items():
                if z3.is_true(model.eval(edge, model_completion=True)):
                    addConn((r, c), (r + 1, c))

            if start not in adjacency:
                raise Exception("Wizard start is not part of the solution path.")

            path = [start]
            previous = None
            current = start
            validPath = True

            for _ in range(rows * cols + 1):
                neighbors = adjacency.get(current, [])
                if len(neighbors) != 2:
                    validPath = False
                    break

                nextCell = neighbors[1] if neighbors[0] == previous else neighbors[0]

                if nextCell == start:
                    # Loop closed — do NOT append start again; the cycle is done
                    break

                if nextCell in path:
                    validPath = False
                    break

                path.append(nextCell)
                previous = current
                current = nextCell

            usedCells = set(adjacency.keys())
            pathCells = set(path)

            if validPath and usedCells == pathCells:
                break

            # Block this exact assignment and retry
            block = []
            for edge in horizontalEdges.values():
                block.append(edge != model.eval(edge, model_completion=True))
            for edge in verticalEdges.values():
                block.append(edge != model.eval(edge, model_completion=True))
            s.add(Or(block))

        # ── FIX 2 ──────────────────────────────────────────────────────────────
        # Convert path to moves WITHOUT appending a final return-to-start step.
        # path = [start, a, b, ..., z]  (start is NOT duplicated at the end)
        # The game detects loop closure automatically; physically stepping on
        # start a second time triggers "visited same location more than once".
        moves = []
        for i in range(len(path) - 1):
            r1, c1 = path[i]
            r2, c2 = path[i + 1]

            if   r2 == r1 - 1 and c2 == c1:     moves.append(WizardMoves.UP)
            elif r2 == r1 + 1 and c2 == c1:     moves.append(WizardMoves.DOWN)
            elif r2 == r1 and c2 == c1 - 1:     moves.append(WizardMoves.LEFT)
            elif r2 == r1 and c2 == c1 + 1:     moves.append(WizardMoves.RIGHT)
            else:
                raise Exception("Invalid move in path.")

        # Add the final step back to start to close the magic circle
        r1, c1 = path[-1]
        r2, c2 = start
        if   r2 == r1 - 1 and c2 == c1:     moves.append(WizardMoves.UP)
        elif r2 == r1 + 1 and c2 == c1:     moves.append(WizardMoves.DOWN)
        elif r2 == r1 and c2 == c1 - 1:     moves.append(WizardMoves.LEFT)
        elif r2 == r1 and c2 == c1 + 1:     moves.append(WizardMoves.RIGHT)
        else:
            raise Exception("Cannot close loop back to start.")

        self.plan = moves
        self.finished = False

        move = self.plan.pop(0)
        if len(self.plan) == 0:
            self.finished = True

        return move



class SpellCastingPuzzleWizard(WizardAgent):

    def react(self, state: GameState) -> GameAction:
        fire_stones = state.get_all_tile_locations(FireStone)
        ice_stones = state.get_all_tile_locations(IceStone)
        neutral_stones = state.get_all_tile_locations(NeutralStone)

        grid_size = state.grid_size
        wizard_location = state.active_entity_location

        # TODO: YOUR CODE HERE
        return MASYU_2_SOLUTION.pop(0)






"""
Here are some reference solutions for some of the included puzzle maps you can use to help you test things
"""

MASYU_1_SOLUTION =[WizardMoves.RIGHT,WizardMoves.UP,WizardMoves.RIGHT,WizardMoves.RIGHT,WizardMoves.RIGHT,WizardMoves.RIGHT,WizardMoves.DOWN,WizardMoves.LEFT,WizardMoves.LEFT,WizardMoves.DOWN,WizardMoves.DOWN,WizardMoves.DOWN,WizardMoves.RIGHT,WizardMoves.UP,WizardMoves.UP,WizardMoves.RIGHT,WizardMoves.RIGHT,WizardMoves.RIGHT,WizardMoves.DOWN,WizardMoves.LEFT,WizardMoves.LEFT,WizardMoves.DOWN,WizardMoves.DOWN,WizardMoves.DOWN,WizardMoves.RIGHT,WizardMoves.RIGHT,WizardMoves.UP,WizardMoves.UP,WizardMoves.RIGHT,WizardMoves.UP,WizardMoves.UP,WizardMoves.UP,WizardMoves.LEFT,WizardMoves.LEFT,WizardMoves.UP,WizardMoves.RIGHT,WizardMoves.RIGHT,WizardMoves.RIGHT,WizardMoves.DOWN,WizardMoves.DOWN,WizardMoves.DOWN,WizardMoves.DOWN,WizardMoves.DOWN,WizardMoves.LEFT,WizardMoves.DOWN,WizardMoves.RIGHT,WizardMoves.DOWN,WizardMoves.DOWN,WizardMoves.DOWN,WizardMoves.LEFT,WizardMoves.LEFT,WizardMoves.LEFT,WizardMoves.LEFT,WizardMoves.UP,WizardMoves.RIGHT,WizardMoves.RIGHT,WizardMoves.RIGHT,WizardMoves.UP,WizardMoves.LEFT,WizardMoves.LEFT,WizardMoves.LEFT,WizardMoves.LEFT,WizardMoves.DOWN,WizardMoves.DOWN,WizardMoves.LEFT,WizardMoves.LEFT,WizardMoves.UP,WizardMoves.UP,WizardMoves.UP,WizardMoves.RIGHT,WizardMoves.RIGHT,WizardMoves.UP,WizardMoves.LEFT,WizardMoves.LEFT,WizardMoves.LEFT,WizardMoves.DOWN,WizardMoves.DOWN,WizardMoves.DOWN,WizardMoves.LEFT,WizardMoves.UP,WizardMoves.UP,WizardMoves.UP,WizardMoves.UP,WizardMoves.RIGHT,WizardMoves.RIGHT,WizardMoves.UP,WizardMoves.UP,WizardMoves.LEFT,WizardMoves.LEFT,WizardMoves.UP]


MASYU_2_SOLUTION =[WizardMoves.RIGHT,WizardSpells.FIREBALL,WizardMoves.DOWN,WizardMoves.DOWN,WizardMoves.RIGHT,WizardMoves.UP,WizardMoves.UP,WizardMoves.RIGHT,WizardMoves.DOWN,WizardMoves.DOWN,WizardMoves.RIGHT,WizardMoves.RIGHT,WizardMoves.RIGHT,WizardMoves.RIGHT,WizardMoves.UP,WizardMoves.LEFT,WizardMoves.LEFT,WizardMoves.LEFT,WizardMoves.UP,WizardMoves.RIGHT,WizardMoves.RIGHT,WizardMoves.RIGHT,WizardMoves.RIGHT,WizardMoves.DOWN,WizardMoves.DOWN,WizardMoves.DOWN,WizardMoves.DOWN,WizardMoves.DOWN,WizardMoves.DOWN,WizardMoves.DOWN,WizardMoves.DOWN,WizardMoves.DOWN,WizardMoves.LEFT,WizardMoves.UP,WizardMoves.UP,WizardMoves.UP,WizardMoves.LEFT,WizardMoves.LEFT,WizardMoves.DOWN,WizardMoves.RIGHT,WizardMoves.DOWN,WizardMoves.DOWN,WizardMoves.LEFT,WizardMoves.LEFT,WizardMoves.UP,WizardMoves.UP,WizardMoves.UP,WizardMoves.UP,WizardMoves.RIGHT,WizardMoves.UP,WizardMoves.RIGHT,WizardMoves.RIGHT,WizardMoves.UP,WizardMoves.LEFT,WizardMoves.LEFT,WizardMoves.LEFT,WizardMoves.DOWN,WizardMoves.LEFT,WizardMoves.LEFT,WizardMoves.UP,WizardMoves.LEFT,WizardMoves.DOWN,WizardMoves.DOWN,WizardMoves.RIGHT,WizardMoves.RIGHT,WizardMoves.DOWN,WizardSpells.FREEZE,WizardMoves.DOWN,WizardMoves.DOWN,WizardMoves.DOWN,WizardMoves.LEFT,WizardMoves.LEFT,WizardMoves.LEFT,WizardMoves.LEFT,WizardMoves.UP,WizardMoves.RIGHT,WizardMoves.RIGHT,WizardMoves.RIGHT,WizardMoves.UP,WizardMoves.UP,WizardMoves.LEFT,WizardMoves.LEFT,WizardMoves.DOWN,WizardMoves.LEFT,WizardMoves.UP,WizardMoves.UP,WizardMoves.RIGHT,WizardMoves.UP,WizardMoves.UP,WizardMoves.UP,WizardMoves.LEFT,WizardMoves.UP,WizardMoves.UP,WizardSpells.FIREBALL,WizardMoves.RIGHT]
