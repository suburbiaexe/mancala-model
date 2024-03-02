## Project Objective

We tried to model the game of mancala. This game involves two players, a board with
two rows of six pits and two large wells (on the end of each row), and marbles; each
player has a row and well specific to them, and the game starts with 4 marbles in
each pit. Mancala is essentially a counting game, where every turn, a player
chooses one of their pits with marbles and disperses the marbles into every succeeding
pit and their own well (if there are enough marbles) one by one, and the game is
finished when there are no more marbles in the pits and they're all split between
the wells. The last move involves the opposing player having no more marbles in any of their pits, and the other player taking the rest of the marbles in their pits and adding it all to their well. A player wins by having the most marbles in their well.

For the most part, the rules of the game are simple: disperse your marbles one by
one, and your turn is over when you are out of marbles to disperse. However, if
your last marble to disperse lands in your well, you get another turn. Also,
if your last marble lands in an empty pit in your row, you can steal the marbles
from your opponent's pit across from the empty pit (if there are marbles there),
and all of those marbles can be added to your well (but this is also a turn-ending
move).

## Model Design and Visualization

Overall, the design of our model uses the tic-tac-toe model from class/lab as inspiration, since we also have a two-player game with a grid-like board (save for the wells). However, there's more complexity in the way players can move in mancala, so we'll touch on some of the specific design choices we made to try and model this game.

When creating our game board, we made the `board` field (of the `Board` sig) a partial function from `Player` to `Int` to `Int` so we could more easily track which pits belonged to which player, rather than making a basic 2x6 grid and remembering which indices belonged to which player. This made it easier to be explicit about whose column (pit) we needed to access in `moveCases`.

`moveCases` was our solution to try to account for the amount of marbles moved throughout the board depending on the type of move that a player made. We thought this would be pretty simple to write, because there aren't _that_ many cases, and this is really just a counting problem, but it ended up being more complex than we thought it would be, because we needed to account for different amounts of overflow as well as stealing. We've left comments in the code on each case, but the gist of our thinking about this predicate was that we wanted to handle moves by saying "if we have a certain amount of marbles, then we want to add this many marbles to all of our pits, this many marbles to our opponent's pits, and this many marbles to our well." Our counting for this method is still a bit off, but we really did our best to handle all the cases numerically. Here is what we needed to account for:

-   If the player only has enough marbles in their selected pit to disperse to some of their subsequent pits
-   If the player has enough marbles in their selected pit to add a marble to their well (which is at the end of their row)
-   If the player has marbles leftover after adding a marble to their well to disperse their marbles in the other player's pits
-   If the player has marbles leftover after dispersing their marbles in the other player's pits to loop back around and disperse in their pits
-   If the player has marbles leftover after dispersing their marbles in their own pits again and can disperse more of their marbles into their well
-   If the player's last dispersed marble lands in an empty pit on their side across from a pit on the opponent's side that contains marbles, then the player gets to put their last marble as well as all of the opponent's marbles from that pit into their own well.

We condensed these move options into 5 cases, some of which account for more overflow such that a move would make multiple marble-dispersal loops around the board. This predicate is unfortunately behind some bugs you'll see when you run the model; the amount of marbles in the pits right after the first turn from the initial board is too high, the amount of marbles in each player's well is also too high/doesn't add up with the marble movement in the `board` table, and because the model seems to create so much overflow, it's always `P1`s turn. Also, the amount of marbles in the wells will sometimes decrease. We couldn't figure out why this happens, but we do have a constraint against this in our `move` predicate (commented out) that, when uncommented, will show that the count of marbles in each well is 0 for every turn for each player. Despite the fact that we weren't able to fully fix this predicate, we couldn't think of a better way to handle this logic, because we can't really implement "loop through the board and add a marble to the pit you're on if you still have marbles" in a modeling language the way we would in another programming language like python. There's no concept of mutable variables/storage in froglet as far as we could tell, so it made the most sense to use this counting solution, which again, even though doesn't work perfectly and is pretty long/complex, is actually made easier and clearer with our `board` mapping, because we don't need to do any unnecessary index subtraction to access the correct opponent pit indices.

`move` itself is a pretty simple predicate/process; players can make moves as long as the game hasn't been won or tied, and the columns (pits) they want to choose from are within the board. We also chose to specifically account for the last move (i.e. if your opponent has no more marbles in any of their pits, all the remaining marbles in your pits get added to your well) in this predicate, because we made `winning` and `tied` really simple, and just checked that all the pits were empty and one of the players had more marbles in their well than the other (or that both players had the same amount of marbles in their wells). So, we checked the last move in `move` so that once a player had won or tied, the predicate would fail and the trace would move to evaluate `doNothing` instead, which is the do-nothing state of the game when it has finally ended.

We also had to include this `doNothing` predicate, because mancala doesn't necessarily end in a set maximum amount of turns, so when we run our game trace we specify a pretty arbitrary amount of turns for the game to run.

In terms of running the model, we only wrote one simple run statement at the very end, which runs the game trace as well as the predicate that enforces that all boards are well-formed. We didn't create a custom visualizer for this model, so the best way to interpret the results of running it will be looking at the tables. With the tables, you can see the order of game boards and the corresponding player turns by looking at the `next` table and the `turn` table. We've found from testing that the `board` table builds upwards, and that the initial game board is represented by the bottom 12 rows of that table (these rows correspond to the `Board` instance in the `first` table). To interpret a row in the `board` table, the first column tells you which `Board` instance it is; the second tells you which which `Player`'s row you're in; the third tells you the index of the column (aka a given pit in the row); the last column tells you how many marbles are in that pit. Unfortunately, there's an issue in the `board` table, where for some `Board` instances, it doesn't include every pit/column. We couldn't figure out why this issue was occurring, but it makes it so that you can't see the amount of marbles in each pit on the board.

The `turn` table is also important because it tells you whose turn it was on that instance of a board. In the `well` table, you can also see how many marbles are in each `Player`s well depending on the `Board` instance you're on.

When running the model, the amount of `Board`s specified is basically how many turns there will be. We also had to increase the int bitwidth, because there are 48 total marbles in Mancala, and the total amount of marbles in a single pit (as well as the amount of marbles in a well) can get pretty high. The model actually doesn't take too long to run, but to see a full game, you'll likely need to run for 15+ boards. You can run with less, though (like 5), to get the gist of the game.

## Signatures and Predicates

We have an abstract sig `Player`, which just represents a player in the game, and
sigs `P1` and `P2` which extend `Player` and are used as the two players needed to play
the game. We also have a `Board` sig, which represents the game board. This sig has
a `well` field, which maps a `Player` to an `Int`; this is to represent a specific `Player`s well and how many marbles are in it (the `Int`). There's also a `board` field, which maps a `Player` to an `Int` to another `Int`; this mapping represents the mapping from the `Player`s row to a specific pit (which we track as a column) to the number of marbles in that pit. Finally, the sig has a `turn` field, which tells us which `Player`s turn it is.

We have a `wellformed` predicate, which provides the constraints we need to make a well-formed board, as well as an `allBoardsWellformed` predicate, which just ensures that all game boards are in fact well-formed. Then, we have an `init` predicate, which sets the conditions for the initial game board (no marbles in the wells, there are 4 marbles in each pit, and some player has the first turn). We also defined `winning` and `tied` predicates, which define the conditions for a player to have either won the game or tied the game.

`move` defines the conditions which must be true for a player to make a move. This predicate calls upon the `moveCases` predicate, which is a very involved predicate that includes all of the different possible ways (or cases) a player can move and the subsequent amount of marbles that are moved around the board. `moveCases` uses a helper function `overflow`, which returns a number of marbles that can indicate whether the move will result in the player dispersing their marbles on the opposing player's side (i.e. overflowing past their own row). `move` also uses the `nextTurn` predicate, which defines the cases when a player gets another turn (and if those aren't met, then it's the opposing player's turn).

We also wrote a `doNothing` predicate, which just enforces that when the game has either been won or tied, nothing happens to the board afterwards, just in case the game ends earlier than the number of turns we scoped for it.

To actually run the game, we made a `Game` sig with a `first` `Board` and the `next` `Board` being the turn that follows the first. We also made a `trace` predicate to define the game trace; we initialize the game board, then begin making moves by calling `move` (or doing nothing by calling `doNothing`).

## Testing

"What tests did you write to test your model itself? What tests did you write to verify properties about your domain area? Feel free to give a high-level overview of this."

We tested almost all of our predicates mostly by checking that conditions that didn't satisfy the predicate would return unsat; for example, we gave conditions for a tied board and also said that board was a winning board, then ensured that that test would be unsat. We tried to do this for each constraint of each predicate, but some of them didn't work out.

Even if the implementations were incorrect for `nextTurn` and `doNothing`, the tests we wrote for both functions should've worked based on the function logic, but they didn't, and we couldn't figure out why. Similarly, our tests for `moveCases` all failed; however, we couldn't use "unsat" testing here, because there are so many possible valid move cases, so we wrote "sat" tests instead. There's a lot that could be (and is) wrong in our function, so we're not surprised that these all failed, but we included the tests nonetheless so you can understand what the expected behavior should've been. Note that we only wrote tests for cases 1-3, because cases 4 and 5 are just repeats of case 3 with larger overflows. For case 3, we also didn't write a test for a large amount of overflow that would loop back to the player's own side due to bitwidth restrictions.

We also didn't test the `trace` predicate, because that just represents the game trace, and we weren't sure how to test it.

Most of our tests do pass, but please disregard the warnings when running—we used test expects and a lot of them didn't recognize that we _did in fact_ reference the functions they think we didn't. Also, we didn't test our `overflow` function because we couldn't find any documentation on how to test functions.

## Documentation

Our `mancala.frg` file contains comments describing any functions/predicates/sigs, as well as some comments within preds when the logic is complex. We've also left some comments in our test file showing which tests don't work.
