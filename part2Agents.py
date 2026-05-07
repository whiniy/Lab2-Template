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
from z3 import (BoolVal, IntVal, Solver, Optimize, Bool, Bools, Int, Ints, Or, Not, And, Implies, Distinct, If, Sum, is_true, sat)


class PuzzleWizard(WizardAgent):
 
    def react(self, state: GameState) -> WizardMoves:
        # do not solve again if we already have a solution
        if hasattr(self, "finished") and self.finished:
            raise Exception("Puzzle already solved; no more moves needed.")

        # keep following the plan if we already have one
        if hasattr(self, "plan") and len(self.plan) > 0:
            move = self.plan.pop(0)

            if len(self.plan) == 0:
                self.finished = True

            return move

        # get all fire stone locations, ice stone locations, and grid size from the state
        fire_stones = state.get_all_tile_locations(FireStone)
        ice_stones = state.get_all_tile_locations(IceStone)
        grid_size = state.grid_size

        # if grid_size is a tuple, unpact it into rows and cols
        # else, assume single integer for rows and cols
        if isinstance(grid_size, tuple):
            rows, cols = grid_size
        else:
            rows = grid_size
            cols = grid_size

        # get wizard location from the state and starting location for the puzzle
        wizard_location = state.active_entity_location
        start = (wizard_location.row, wizard_location.col)

        # combine fire and ice stone locations into a single set of all stone locations
        all_stone_locations = set()
        for stone in fire_stones:
            all_stone_locations.add((stone.row, stone.col))
        for stone in ice_stones:
            all_stone_locations.add((stone.row, stone.col))

        s = Solver()

        horizontalEdges = {}
        verticalEdges = {}

        # create all possible horizontal and vertical edges as boolean variables
        for row in range(rows):
            for col in range(cols):
                if col < cols - 1:
                    horizontalEdges[(row, col)] = Bool(f"h{row}_{col}")
                if row < rows - 1:
                    verticalEdges[(row, col)] = Bool(f"v{row}_{col}")

        # helper function to get all edges touching a cell at (r, c)
        def isTouching(r, c):
            edges = []

            # left horizontal edge
            if (r, c - 1) in horizontalEdges:
                edges.append(horizontalEdges[(r, c - 1)])
            # right horizontal edge
            if (r, c) in horizontalEdges:
                edges.append(horizontalEdges[(r, c)])
            # up vertical edge
            if (r - 1, c) in verticalEdges:
                edges.append(verticalEdges[(r - 1, c)])
            # down vertical edge
            if (r, c) in verticalEdges:
                edges.append(verticalEdges[(r, c)])

            return edges

        # helper function to count number of edges in a list that are True in the model
        def numEdges(edges):
            return sum([If(edge, 1, 0) for edge in edges])

        # helper function to get every directional edge for a cell at (r, c)
        def directionalEdges(r, c):
            left = horizontalEdges.get((r, c - 1), z3.BoolVal(False))
            right = horizontalEdges.get((r, c), z3.BoolVal(False))
            up = verticalEdges.get((r - 1, c), z3.BoolVal(False))
            down = verticalEdges.get((r, c), z3.BoolVal(False))

            return left, right, up, down

        # helper function to check if a cell at (r, c) is used in the path
        def isUsed(r, c):
            return numEdges(isTouching(r, c)) == 2

        # helper function to check if a cell at (r, c) is part of a straight path
        def isStraight(r, c):
            left, right, up, down = directionalEdges(r, c)

            return Or(And(left, right),
                      And(up, down))

        # helper function to check if a cell at (r, c) is a turn in the path
        def isTurn(r, c):
            left, right, up, down = directionalEdges(r, c)

            return Or(And(left, up),
                      And(left, down),
                      And(right, up),
                      And(right, down))

        # every cell either has 2 edges or is unused
        for row in range(rows):
            for col in range(cols):
                n = numEdges(isTouching(row, col))
                s.add(Or(n == 0, n == 2))

        for row in range(rows):
            for col in range(cols):
                if row == 0 or row == rows - 1 or col == 0 or col == cols - 1:
                    s.add(numEdges(isTouching(row, col)) == 0)

        # wizard starting location must be used in the loop
        s.add(isUsed(start[0], start[1]))

        # every stone location must be used in the loop
        for r, c in all_stone_locations:
            s.add(isUsed(r, c))

        order = {}

        for row in range(rows):
            for col in range(cols):
                order[(row, col)] = Int(f"order_{row}_{col}")

        s.add(order[start] == 0)

        for row in range(rows):
            for col in range(cols):
                current = (row, col)
                s.add(Implies(Not(isUsed(row, col)), order[current] == 0))
                s.add(Implies(isUsed(row, col), And(order[current] >= 0, order[current] <= rows * cols)))

                if current != start:
                    left, right, up, down = directionalEdges(row, col)
                    lower_neighbors = []

                    if col - 1 >= 0:
                        lower_neighbors.append(And(left, order[(row, col - 1)] < order[current]))
                    if col + 1 < cols:
                        lower_neighbors.append(And(right, order[(row, col + 1)] < order[current]))
                    if row - 1 >= 0:
                        lower_neighbors.append(And(up, order[(row - 1, col)] < order[current]))
                    if row + 1 < rows:
                        lower_neighbors.append(And(down, order[(row + 1, col)] < order[current]))

                    s.add(Implies(isUsed(row, col), And(order[current] > 0, Or(*lower_neighbors))))

        # fire stone constraints
        for stone in fire_stones:
            r = stone.row
            c = stone.col

            left, right, up, down = directionalEdges(r, c)

            # fire stone must be a turn
            s.add(isTurn(r, c))

            # if fire stone turns left + up,
            # left + upper neighbor cells must be straight
            s.add(Implies(And(left, up),
                          And(isStraight(r, c - 1), isStraight(r - 1, c))))
            # if fire stone turns left + down
            s.add(Implies(And(left, down),
                          And(isStraight(r, c - 1), isStraight(r + 1, c))))
            # if fire stone turns right + up
            s.add(Implies(And(right, up),
                          And(isStraight(r, c + 1), isStraight(r - 1, c))))
            # if fire stone turns right + down
            s.add(Implies(And(right, down),
                          And(isStraight(r, c + 1), isStraight(r + 1, c))))

        # ice stone constraints
        for stone in ice_stones:
            r = stone.row
            c = stone.col

            left, right, up, down = directionalEdges(r, c)

            # ice stone must be straight
            s.add(isStraight(r, c))

            # if ice stone goes left-right,
            # at least 1 side neighbor must turn
            s.add(Implies(And(left, right),
                          Or(isTurn(r, c - 1), isTurn(r, c + 1))))

            # if ice stone goes up-down,
            # at least 1 side neighbor must turn
            s.add(Implies(And(up, down),
                          Or(isTurn(r - 1, c), isTurn(r + 1, c))))

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

        for (r, c), edge in horizontalEdges.items():
            if z3.is_true(model.eval(edge, model_completion=True)):
                addConn((r, c), (r, c + 1))

        for (r, c), edge in verticalEdges.items():
            if z3.is_true(model.eval(edge, model_completion=True)):
                addConn((r, c), (r + 1, c))

        if start not in adjacency:
            raise Exception("Wizard start is not part of the solution path.")

        # from the start, trace loop
        path = [start]
        previous = None
        current = start
        closedLoop = False

        for _ in range(rows * cols + 1):
            neighbors = adjacency.get(current, [])

            if len(neighbors) != 2:
                raise Exception("Invalid solution: path cell does not have exactly 2 neighbors.")

            if previous is None:
                nextCell = neighbors[0]
            else:
                if neighbors[0] == previous:
                    nextCell = neighbors[1]
                else:
                    nextCell = neighbors[0]

            if nextCell == start:
                closedLoop = True
                break

            if nextCell in path:
                raise Exception(f"Invalid solution: path revisits {nextCell} before closing.")

            path.append(nextCell)
            previous = current
            current = nextCell

        if not closedLoop:
            raise Exception("Invalid solution: loop did not return to start.")

        usedCells = set(adjacency.keys())
        pathCells = set(path)

        if usedCells != pathCells:
            raise Exception("Invalid solution: there are disconnected path cells.")

        if not all_stone_locations.issubset(pathCells):
            missing = all_stone_locations - pathCells
            raise Exception(f"Invalid solution: missing stones {missing}")

        # close loop by adding start to end of path
        path.append(start)

        possible_moves = [
            WizardMoves.UP,
            WizardMoves.DOWN,
            WizardMoves.LEFT,
            WizardMoves.RIGHT
        ]

        # convert path into wizard moves
        moves = []

        for i in range(len(path) - 1):
            r1, c1 = path[i]
            r2, c2 = path[i + 1]

            dr = r2 - r1
            dc = c2 - c1

            foundMove = None

            for move in possible_moves:
                move_dr, move_dc = move.value
                if move_dr == dr and move_dc == dc:
                    foundMove = move
                    break

            if foundMove is None:
                print("MOVE VALUES:", [(move, move.value) for move in possible_moves])
                print("FAILED PATH STEP:", (r1, c1), "to", (r2, c2))
                print("FULL PATH:", path)
                raise Exception("Could not convert Z3 path step into a real WizardMove.")

            moves.append(foundMove)

        # verify that the moves correctly simulate the path
        simulated = [start]
        current = start

        for move in moves:
            move_dr, move_dc = move.value
            current = (current[0] + move_dr, current[1] + move_dc)
            simulated.append(current)

        if simulated != path:
            print("MOVE VALUES:", [(move, move.value) for move in possible_moves])
            print("Z3 PATH:", path)
            print("SIMULATED PATH:", simulated)
            raise Exception("Move conversion does not match Z3 path.")

        visited = set()

        for cell in simulated[:-1]:
            if cell in visited:
                print("SIMULATED PATH:", simulated)
                raise Exception(f"Generated moves revisit {cell} before final close.")
            visited.add(cell)

        if not all_stone_locations.issubset(set(simulated)):
            missing = all_stone_locations - set(simulated)
            raise Exception(f"Generated moves miss stones {missing}")

        self.plan = moves
        self.finished = False

        move = self.plan.pop(0)

        if len(self.plan) == 0:
            self.finished = True

        return move


class SpellCastingPuzzleWizard(WizardAgent):

    def react(self, state: GameState) -> GameAction:
        # keep following the plan if we already have one
        if hasattr(self, "plan") and len(self.plan) > 0:
            return self.plan.pop(0)

        # get stone locations
        fire_stones = state.get_all_tile_locations(FireStone)
        ice_stones = state.get_all_tile_locations(IceStone)
        neutral_stones = state.get_all_tile_locations(NeutralStone)

        grid_size = state.grid_size

        if isinstance(grid_size, tuple):
            rows, cols = grid_size
        else:
            rows = grid_size
            cols = grid_size

        wizard_location = state.active_entity_location
        start = (wizard_location.row, wizard_location.col)

        # store original stone types as tuple locations
        original_types = {}

        for stone in fire_stones:
            original_types[(stone.row, stone.col)] = "fire"

        for stone in ice_stones:
            original_types[(stone.row, stone.col)] = "ice"

        for stone in neutral_stones:
            original_types[(stone.row, stone.col)] = "neutral"

        all_stone_locations = set(original_types.keys())

        s = Solver()

        horizontalEdges = {}
        verticalEdges = {}

        # create all possible horizontal and vertical edges
        for row in range(rows):
            for col in range(cols):
                if col < cols - 1:
                    horizontalEdges[(row, col)] = Bool(f"h_{row}_{col}")

                if row < rows - 1:
                    verticalEdges[(row, col)] = Bool(f"v_{row}_{col}")

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
            return Sum([If(edge, 1, 0) for edge in edges])

        def directionalEdges(r, c):
            left = horizontalEdges.get((r, c - 1), BoolVal(False))
            right = horizontalEdges.get((r, c), BoolVal(False))
            up = verticalEdges.get((r - 1, c), BoolVal(False))
            down = verticalEdges.get((r, c), BoolVal(False))

            return left, right, up, down

        def isUsed(r, c):
            return numEdges(isTouching(r, c)) == 2

        def isStraight(r, c):
            left, right, up, down = directionalEdges(r, c)

            return Or(
                And(left, right),
                And(up, down)
            )

        def isTurn(r, c):
            left, right, up, down = directionalEdges(r, c)

            return Or(
                And(left, up),
                And(left, down),
                And(right, up),
                And(right, down)
            )

        # every cell is either unused or has exactly 2 edges
        for row in range(rows):
            for col in range(cols):
                n = numEdges(isTouching(row, col))
                s.add(Or(n == 0, n == 2))

        # wizard start must be part of the loop
        s.add(isUsed(start[0], start[1]))

        # every stone must be used
        for r, c in all_stone_locations:
            s.add(isUsed(r, c))

        # order variables prevent disconnected loops
        order = {}

        for row in range(rows):
            for col in range(cols):
                order[(row, col)] = Int(f"order_{row}_{col}")

        s.add(order[start] == 0)

        for row in range(rows):
            for col in range(cols):
                current = (row, col)

                s.add(Implies(Not(isUsed(row, col)), order[current] == 0))
                s.add(Implies(isUsed(row, col), And(order[current] >= 0, order[current] <= rows * cols)))

                if current != start:
                    left, right, up, down = directionalEdges(row, col)
                    lower_neighbors = []

                    if col - 1 >= 0:
                        lower_neighbors.append(
                            And(left, order[(row, col - 1)] < order[current])
                        )

                    if col + 1 < cols:
                        lower_neighbors.append(
                            And(right, order[(row, col + 1)] < order[current])
                        )

                    if row - 1 >= 0:
                        lower_neighbors.append(
                            And(up, order[(row - 1, col)] < order[current])
                        )

                    if row + 1 < rows:
                        lower_neighbors.append(
                            And(down, order[(row + 1, col)] < order[current])
                        )

                    s.add(
                        Implies(
                            isUsed(row, col),
                            And(order[current] > 0, Or(*lower_neighbors))
                        )
                    )

        # True means the final stone type is fire.
        # False means the final stone type is ice.
        finalIsFire = {}

        for r, c in all_stone_locations:
            finalIsFire[(r, c)] = Bool(f"final_fire_{r}_{c}")

        # add fire/ice behavior constraints depending on final stone type
        for r, c in all_stone_locations:
            left, right, up, down = directionalEdges(r, c)

            fire_rule = And(
                isTurn(r, c),

                Implies(
                    And(left, up),
                    And(isStraight(r, c - 1), isStraight(r - 1, c))
                ),

                Implies(
                    And(left, down),
                    And(isStraight(r, c - 1), isStraight(r + 1, c))
                ),

                Implies(
                    And(right, up),
                    And(isStraight(r, c + 1), isStraight(r - 1, c))
                ),

                Implies(
                    And(right, down),
                    And(isStraight(r, c + 1), isStraight(r + 1, c))
                )
            )

            ice_rule = And(
                isStraight(r, c),

                Implies(
                    And(left, right),
                    Or(isTurn(r, c - 1), isTurn(r, c + 1))
                ),

                Implies(
                    And(up, down),
                    Or(isTurn(r - 1, c), isTurn(r + 1, c))
                )
            )

            s.add(Implies(finalIsFire[(r, c)], fire_rule))
            s.add(Implies(Not(finalIsFire[(r, c)]), ice_rule))

        # mana cost expression
        cost_terms = []

        for loc in all_stone_locations:
            original = original_types[loc]

            if original == "fire":
                # fire costs 0
                # ice costs 10
                cost_terms.append(If(finalIsFire[loc], 0, 10))

            elif original == "ice":
                # ice costs 0
                # fire costs 15
                cost_terms.append(If(finalIsFire[loc], 15, 0))

            else:
                # ice costs 10
                # fire costs 15
                cost_terms.append(If(finalIsFire[loc], 15, 10))

        if len(cost_terms) > 0:
            total_cost = Sum(cost_terms)
        else:
            total_cost = IntVal(0)

        # Generate all possible mana costs.
        possible_costs = {0}

        for loc in all_stone_locations:
            original = original_types[loc]

            if original == "fire":
                choices = [0, 10]
            elif original == "ice":
                choices = [0, 15]
            else:
                choices = [10, 15]

            new_costs = set()

            for old_cost in possible_costs:
                for choice in choices:
                    new_costs.add(old_cost + choice)

            possible_costs = new_costs

        possible_costs = sorted(possible_costs)

        model = None

        for target_cost in possible_costs:
            s.push()
            s.add(total_cost == target_cost)

            if s.check() == sat:
                model = s.model()
                s.pop()
                break

            s.pop()

        if model is None:
            return WizardMoves.UP

        # build final spell changes from the model
        spell_changes = {}

        for loc in all_stone_locations:
            final_fire = is_true(model.eval(finalIsFire[loc], model_completion=True))
            original = original_types[loc]

            if final_fire:
                if original != "fire":
                    spell_changes[loc] = WizardSpells.FIREBALL
            else:
                if original != "ice":
                    spell_changes[loc] = WizardSpells.FREEZE

        # create adjacency from chosen edges
        adjacency = {}

        def addConn(a, b):
            if a not in adjacency:
                adjacency[a] = []

            if b not in adjacency:
                adjacency[b] = []

            adjacency[a].append(b)
            adjacency[b].append(a)

        for (r, c), edge in horizontalEdges.items():
            if is_true(model.eval(edge, model_completion=True)):
                addConn((r, c), (r, c + 1))

        for (r, c), edge in verticalEdges.items():
            if is_true(model.eval(edge, model_completion=True)):
                addConn((r, c), (r + 1, c))

        if start not in adjacency:
            return WizardMoves.UP

        # trace the loop from the start
        path = [start]
        previous = None
        current = start
        closedLoop = False

        for _ in range(rows * cols + 1):
            neighbors = adjacency.get(current, [])

            if len(neighbors) != 2:
                return WizardMoves.UP

            if previous is None:
                nextCell = neighbors[0]
            else:
                if neighbors[0] == previous:
                    nextCell = neighbors[1]
                else:
                    nextCell = neighbors[0]

            if nextCell == start:
                closedLoop = True
                break

            if nextCell in path:
                return WizardMoves.UP

            path.append(nextCell)
            previous = current
            current = nextCell

        if not closedLoop:
            return WizardMoves.UP

        usedCells = set(adjacency.keys())
        pathCells = set(path)

        if usedCells != pathCells:
            return WizardMoves.UP

        if not all_stone_locations.issubset(pathCells):
            return WizardMoves.UP

        # close loop by adding start to end
        path.append(start)

        possible_moves = [
            WizardMoves.UP,
            WizardMoves.DOWN,
            WizardMoves.LEFT,
            WizardMoves.RIGHT
        ]

        moves = []

        for i in range(len(path) - 1):
            r1, c1 = path[i]
            r2, c2 = path[i + 1]

            dr = r2 - r1
            dc = c2 - c1

            foundMove = None

            for move in possible_moves:
                move_dr, move_dc = move.value

                if move_dr == dr and move_dc == dc:
                    foundMove = move
                    break

            if foundMove is None:
                return WizardMoves.UP

            moves.append(foundMove)

        # add spells into the movement plan
        plan = []
        already_cast = set()

        # if the starting tile needs a spell, cast immediately
        if path[0] in spell_changes:
            plan.append(spell_changes[path[0]])
            already_cast.add(path[0])

        for i in range(len(moves)):
            destination = path[i + 1]

            # cast before stepping onto the destination stone
            if destination in spell_changes and destination not in already_cast:
                plan.append(spell_changes[destination])
                already_cast.add(destination)

            plan.append(moves[i])

        self.plan = plan

        if len(self.plan) == 0:
            return WizardMoves.UP

        return self.plan.pop(0)


"""
Here are some reference solutions for some of the included puzzle maps you can use to help you test things
"""

MASYU_1_SOLUTION =[WizardMoves.RIGHT,WizardMoves.UP,WizardMoves.RIGHT,WizardMoves.RIGHT,WizardMoves.RIGHT,WizardMoves.RIGHT,WizardMoves.DOWN,WizardMoves.LEFT,WizardMoves.LEFT,WizardMoves.DOWN,WizardMoves.DOWN,WizardMoves.DOWN,WizardMoves.RIGHT,WizardMoves.UP,WizardMoves.UP,WizardMoves.RIGHT,WizardMoves.RIGHT,WizardMoves.RIGHT,WizardMoves.DOWN,WizardMoves.LEFT,WizardMoves.LEFT,WizardMoves.DOWN,WizardMoves.DOWN,WizardMoves.DOWN,WizardMoves.RIGHT,WizardMoves.RIGHT,WizardMoves.UP,WizardMoves.UP,WizardMoves.RIGHT,WizardMoves.UP,WizardMoves.UP,WizardMoves.UP,WizardMoves.LEFT,WizardMoves.LEFT,WizardMoves.UP,WizardMoves.RIGHT,WizardMoves.RIGHT,WizardMoves.RIGHT,WizardMoves.DOWN,WizardMoves.DOWN,WizardMoves.DOWN,WizardMoves.DOWN,WizardMoves.DOWN,WizardMoves.LEFT,WizardMoves.DOWN,WizardMoves.RIGHT,WizardMoves.DOWN,WizardMoves.DOWN,WizardMoves.DOWN,WizardMoves.LEFT,WizardMoves.LEFT,WizardMoves.LEFT,WizardMoves.LEFT,WizardMoves.UP,WizardMoves.RIGHT,WizardMoves.RIGHT,WizardMoves.RIGHT,WizardMoves.UP,WizardMoves.LEFT,WizardMoves.LEFT,WizardMoves.LEFT,WizardMoves.LEFT,WizardMoves.DOWN,WizardMoves.DOWN,WizardMoves.LEFT,WizardMoves.LEFT,WizardMoves.UP,WizardMoves.UP,WizardMoves.UP,WizardMoves.RIGHT,WizardMoves.RIGHT,WizardMoves.UP,WizardMoves.LEFT,WizardMoves.LEFT,WizardMoves.LEFT,WizardMoves.DOWN,WizardMoves.DOWN,WizardMoves.DOWN,WizardMoves.LEFT,WizardMoves.UP,WizardMoves.UP,WizardMoves.UP,WizardMoves.UP,WizardMoves.RIGHT,WizardMoves.RIGHT,WizardMoves.UP,WizardMoves.UP,WizardMoves.LEFT,WizardMoves.LEFT,WizardMoves.UP]


MASYU_2_SOLUTION =[WizardMoves.RIGHT,WizardSpells.FIREBALL,WizardMoves.DOWN,WizardMoves.DOWN,WizardMoves.RIGHT,WizardMoves.UP,WizardMoves.UP,WizardMoves.RIGHT,WizardMoves.DOWN,WizardMoves.DOWN,WizardMoves.RIGHT,WizardMoves.RIGHT,WizardMoves.RIGHT,WizardMoves.RIGHT,WizardMoves.UP,WizardMoves.LEFT,WizardMoves.LEFT,WizardMoves.LEFT,WizardMoves.UP,WizardMoves.RIGHT,WizardMoves.RIGHT,WizardMoves.RIGHT,WizardMoves.RIGHT,WizardMoves.DOWN,WizardMoves.DOWN,WizardMoves.DOWN,WizardMoves.DOWN,WizardMoves.DOWN,WizardMoves.DOWN,WizardMoves.DOWN,WizardMoves.DOWN,WizardMoves.DOWN,WizardMoves.LEFT,WizardMoves.UP,WizardMoves.UP,WizardMoves.UP,WizardMoves.LEFT,WizardMoves.LEFT,WizardMoves.DOWN,WizardMoves.RIGHT,WizardMoves.DOWN,WizardMoves.DOWN,WizardMoves.LEFT,WizardMoves.LEFT,WizardMoves.UP,WizardMoves.UP,WizardMoves.UP,WizardMoves.UP,WizardMoves.RIGHT,WizardMoves.UP,WizardMoves.RIGHT,WizardMoves.RIGHT,WizardMoves.UP,WizardMoves.LEFT,WizardMoves.LEFT,WizardMoves.LEFT,WizardMoves.DOWN,WizardMoves.LEFT,WizardMoves.LEFT,WizardMoves.UP,WizardMoves.LEFT,WizardMoves.DOWN,WizardMoves.DOWN,WizardMoves.RIGHT,WizardMoves.RIGHT,WizardMoves.DOWN,WizardSpells.FREEZE,WizardMoves.DOWN,WizardMoves.DOWN,WizardMoves.DOWN,WizardMoves.LEFT,WizardMoves.LEFT,WizardMoves.LEFT,WizardMoves.LEFT,WizardMoves.UP,WizardMoves.RIGHT,WizardMoves.RIGHT,WizardMoves.RIGHT,WizardMoves.UP,WizardMoves.UP,WizardMoves.LEFT,WizardMoves.LEFT,WizardMoves.DOWN,WizardMoves.LEFT,WizardMoves.UP,WizardMoves.UP,WizardMoves.RIGHT,WizardMoves.UP,WizardMoves.UP,WizardMoves.UP,WizardMoves.LEFT,WizardMoves.UP,WizardMoves.UP,WizardSpells.FIREBALL,WizardMoves.RIGHT]
