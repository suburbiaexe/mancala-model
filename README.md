## Project Objective

We tried to model the game of mancala. This game involves two players, a board with
two rows of six pits and two large wells (on the side of the rows), and marbles; each
player has a row and well specific to them, and the game starts with 4 marbles in
each pit. Mancala is essentially a counting game, where every turn, a player
chooses one of their pits with marbles and disperses the marbles into every succeeding
pit and their own well (if there are enough marbles) one by one, and the game is
finished when there are no more marbles in the pits and they're all split between
the wells. A player wins by having the most marbles in their well.

For the most part, the rules of the game are simple: disperse your marbles one by
one, and your turn is over when you are out of marbles to disperse. However, if
your last marble to disperse lands in your well, you get another turn. Also,
if your last marble lands in an empty pit in your row, you can steal the marbles
from your opponent's pit across from the empty pit (if there are marbles there),
and all of those marbles can be added to your well (but this is also a turn-ending
move).

## Model Design and Visualization

"Give an overview of your model design choices, what checks or run statements you wrote, and what we should expect to see from an instance produced by the Sterling visualizer. How should we look at and interpret an instance created by your spec? Did you create a custom visualization, or did you use the default?"

When creating our game board, we made the `board` field (of the `Board` sig) a partial function from `Player` to `Int` to `Int` so we could more easily track which pits belonged to which player, rather than making a basic 2x6 grid and remembering which indices belonged to which player. This made it easier to be explicit about whose column (pit) we needed to access in `moveCases`.

`moveCases` was our solution to try to account for the amount of marbles moved throughout the board depending on the type of move that a player made. We thought this would be pretty simple to write, because there aren't _that_ many cases, and this is really just a counting problem, but it ended up being more complex than we thought it would be, because we needed to account for different amounts of overflow as well as stealing.

## Signatures and Predicates

We have an abstract sig `Player`, which just represents a player in the game, and
sigs `P1` and `P2` which extend `Player` and are used as the two players needed to play
the game. We also have a `Board` sig, which represents the game board. This sig has
a `well` field, which maps a `Player` to an `Int`; this is to represent a specific `Player`s well and how many marbles are in it (the `Int`). There's also a `board` field, which maps a `Player` to an `Int` to another `Int`; this mapping represents the mapping from the `Player`s row to a specific pit (which we track as a column) to the number of marbles in that pit. Finally, the sig has a `turn` field, which tells us which `Player`s turn it is.

We have a `wellformed` predicate, which provides the constraints we need to make a well-formed board, as well as an `allBoardsWellformed` predicate, which just ensures that all game boards are in fact well-formed. Then, we have an `init` predicate, which sets the conditions for the initial game board (no marbles in the wells, there are 4 marbles in each pit, and some player has the first turn). We also defined `winning` and `tied` predicates, which define the conditions for a player to have either won the game or tied the game.

`move` defines the conditions which must be true for a player to make a move. This predicate calls upon the `moveCases` predicate, which is a very involved predicate that includes all of the different possible ways (or cases) a player can move and the subsequent amount of marbles that are moved around the board. `moveCases` uses a helper function `overflow`, which returns a number of marbles that can indicate whether the move will result in the player dispersing their marbles on the opposing player's side (i.e. overflowing past their own row), as well as the `addToWell` predicate, which adds extra marbles to the player's well in the cases where they have a very large sum of marbles to disperse which would loop back around to their own well at least once. `move` also uses the `nextTurn` predicate, which defines the cases when a player gets another turn (and if those aren't met, then it's the opposing player's turn).

We also wrote a `doNothing` predicate, which just enforces that when the game has either been won or tied, nothing happens to the board afterwards, just in case the game ends earlier than the number of turns we scoped for it.

To actually run the game, we made a `Game` sig with a `first` `Board` and the `next` `Board` being the turn that follows the first. We also made a `trace` predicate to define the game trace; we initialize the game board, then begin making moves by calling `move` (or doing nothing by calling `doNothing`).

## Testing

"What tests did you write to test your model itself? What tests did you write to verify properties about your domain area? Feel free to give a high-level overview of this."

## Documentation

"Make sure your model and test files are well-documented. This will help in understanding the structure and logic of your project."
