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
        # keep plan saved if we have one, otherwise create a new plan
        if hasattr(self, "plan") and len(self.plan) > 0:
            return self.plan.pop(0)

        # get all fire stone locations on board
        fire_stones = state.get_all_tile_locations(FireStone)
        # get all ice stone locations on board
        ice_stones = state.get_all_tile_locations(IceStone)
        # get grid size
        grid_size = state.grid_size
        # get wizard location
        wizard_location = state.active_entity_location
        # get the starting location of the wizard as (row, col)
        start = (wizard_location.row, wizard_location.col)

        # Z3 solver
        s = Solver()

        # dictionaries to hold boolean variables for horizontal and vertical edges
        horizontalEdges = {}
        verticalEdges = {}

        # create all possible horizontal and vertical edges
        # iterate through each cell of the board
        for row in range(grid_size):
            for col in range(grid_size):
                # horizontal edge - (row, col) to (row, col + 1)
                if col < grid_size - 1:
                    horizontalEdges[(row, col)] = Bool(f"h{row}_{col}")
                # vertical edge - (row, col) to (row + 1, col)
                if row < grid_size - 1:
                    verticalEdges[(row, col)] = Bool(f"v{row}_{col}")

        # get all possible paths touching the cell
        def isTouching(r, c):
            edges = []
            # left edge: (r, c - 1) to (r, c)
            if (r, c - 1) in horizontalEdges:
                edges.append(horizontalEdges[(r, c - 1)])
            # right edge: (r, c) to (r, c + 1)
            if (r, c) in horizontalEdges:
                edges.append(horizontalEdges[(r, c)])
            # up edge: (r - 1, c) to (r, c)
            if (r - 1, c) in verticalEdges:
                edges.append(verticalEdges[(r - 1, c)])
            # down edge: (r, c) to (r + 1, c)
            if (r, c) in verticalEdges:
                edges.append(verticalEdges[(r, c)])

            return edges

        # returns number of edges that are True
        def numEdges(edges):
            return sum([If(edge, 1, 0) for edge in edges])

        # gets every edge in every direction and returns it (left, right, up, down)
        def directionalEdges(r, c):
            left = horizontalEdges.get((r, c - 1), z3.BoolVal(False))
            right = horizontalEdges.get((r, c), z3.BoolVal(False))
            up = verticalEdges.get((r - 1, c), z3.BoolVal(False))
            down = verticalEdges.get((r, c), z3.BoolVal(False))

            return left, right, up, down

        # checks if the path goes straight through a cell
        def isStraight(r, c):
            left, right, up, down = directionalEdges(r, c)

            return Or(And(left, right),
                      And(up, down))

        # checks if a path turns at the cell
        def isTurn(r, c):
            left, right, up, down = directionalEdges(r, c)

            return Or(And(left, up),
                      And(left, down),
                      And(right, up),
                      And(right, down))

        # every cell should have 0 or 2 edges, indicating it's either
        # not part of the path or is part of the path and connects to 2 other cells
        for row in range(grid_size):
            for col in range(grid_size):
                edges = isTouching(row, col)
                n = numEdges(edges)

                s.add(Or(n == 0, n == 2))

        # add wizard's starting position contraint
        s.add(numEdges(isTouching(start[0], start[1])) == 2)

        # fire stones contraints
        for stone in fire_stones:
            r = stone.row
            c = stone.col

            left, right, up, down = directionalEdges(r, c)

            # fire stone must be on the path and must turn
            s.add(numEdges(isTouching(r, c)) == 2)
            s.add(isTurn(r, c))

            # if fire stone connects left and up
            # left and up neighbors must be straight
            s.add(Implies(
                And(left, up),
                And(isStraight(r, c - 1), isStraight(r - 1, c))
            ))

            # if the fire stone connects left + down
            s.add(Implies(
                And(left, down),
                And(isStraight(r, c - 1), isStraight(r + 1, c))
            ))

            # if the fire stone connects right + up
            s.add(Implies(
                And(right, up),
                And(isStraight(r, c + 1), isStraight(r - 1, c))
            ))

            # if the fire stone connects right + down
            s.add(Implies(
                And(right, down),
                And(isStraight(r, c + 1), isStraight(r + 1, c))
            ))

        # ice stones must have 1 neighbor edge that turns and 1 neighbor edge that goes straight
        # ice stone itself must be straight
        for stone in ice_stones:
            r = stone.row
            c = stone.col

            left, right, up, down = directionalEdges(r, c)

            # ice stone must be on the path and must have 2 edges
            # ice stone has to go straight
            s.add(numEdges(isTouching(r, c)) == 2)
            s.add(isStraight(r, c))

            # if ice stone goes left-right
            # left or right neighbor must turn
            s.add(Implies(
                And(left, right),
                Or(isTurn(r, c - 1), isTurn(r, c + 1))
            ))

            # if ice stone goes up-down
            # up or down neighbor must turn
            s.add(Implies(
                And(up, down),
                Or(isTurn(r - 1, c), isTurn(r + 1, c))
            ))

        # find a solution that satisfies all constraints
        while True:
            if s.check() != z3.sat:
                raise Exception("No solution found for this Masyu puzzle.")

            model = s.model()
            adjacency = {}

            def addConn(a, b):
                if a not in adjacency:
                    adjacency[a] = []
                if b not in adjacency:
                    adjacency[b] = []

                adjacency[a].append(b)
                adjacency[b].append(a)

            # add horizontal edges that are True
            for (r, c), edge in horizontalEdges.items():
                if z3.is_true(model.eval(edge, model_completion=True)):
                    addConn((r, c), (r, c + 1))

            # add vertical edges that are True
            for (r, c), edge in verticalEdges.items():
                if z3.is_true(model.eval(edge, model_completion=True)):
                    addConn((r, c), (r + 1, c))

            # trace the loop for the solution and make sure it's valid
            if start not in adjacency:
                raise Exception("Wizard start is not part of the solution path.")

            path = [start]
            previous = None
            current = start

            validPath = True

            for _ in range(grid_size * grid_size + 1):
                neighbors = adjacency[current]

                if len(neighbors) != 2:
                    validPath = False
                    break

                if previous is None:
                    nextCell = neighbors[0]
                else:
                    if neighbors[0] == previous:
                        nextCell = neighbors[1]
                    else:
                        nextCell = neighbors[0]

                if nextCell == start:
                    path.append(start)
                    break

                if nextCell in path:
                    validPath = False
                    break

                path.append(nextCell)
                previous = current
                current = nextCell

            # check if path uses all cells in the solution
            # if not, there are multiple loops
            usedCells = set(adjacency.keys())
            pathCells = set(path)

            if validPath and path[-1] == start and usedCells == pathCells:
                break

            # block if there's multiple disconnected loops
            block = []

            for edge in horizontalEdges.values():
                value = model.eval(edge, model_completion=True)
                block.append(edge != value)

            for edge in verticalEdges.values():
                value = model.eval(edge, model_completion=True)
                block.append(edge != value)

            s.add(Or(block))

        # convert into moves for wizard to take 
        moves = []

        for i in range(len(path) - 1):
            r1, c1 = path[i]
            r2, c2 = path[i + 1]

            if r2 == r1 - 1 and c2 == c1:
                moves.append(WizardMoves.UP)
            elif r2 == r1 + 1 and c2 == c1:
                moves.append(WizardMoves.DOWN)
            elif r2 == r1 and c2 == c1 - 1:
                moves.append(WizardMoves.LEFT)
            elif r2 == r1 and c2 == c1 + 1:
                moves.append(WizardMoves.RIGHT)
            else:
                raise Exception("Invalid move in path.")

        self.plan = moves

        return self.plan.pop(0)



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
