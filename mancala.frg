#lang forge/bsl

abstract sig Player {}
one sig P1, P2 extends Player {}

sig Board {
    -- Player's total number of marbles in well
    well: func Player -> Int,
    -- Player's -> col -> number of marbles in pit (represented by col)
    board: pfunc Player -> Int -> Int,
    -- Which Player's turn is it
    turn: one Player
}

-- Each player has 6 pits on their side of the board
fun COLMIN: one Int { 0 }
fun COLMAX: one Int { 5 }

-- Ensures only valid indices for pits and non-negative numbers of seeds
pred wellformed[b: Board, p, otherP: Player] {
    all col: Int | {
        (col < COLMIN or col > COLMAX) implies 
            no b.board[p][col] and no b.board[otherP][col]
        else
            b.board[p][col] >= 0 and
            b.board[otherP][col] >= 0 and
            b.well[p] >= 0
            b.well[otherP] >= 0
    }
}

pred allBoardsWellformed { all b : Board | wellformed[b, P1, P2] }

-- Initializes a given board with no seeds in each well and 4 seeds in each valid pit
pred init[b: Board, p, otherP: Player] {
    b.well[p] = 0
    b.well[otherP] = 0

    all col: Int | col >= COLMIN and col <= COLMAX => {
        b.board[p][col] = 4
        b.board[otherP][col] = 4
    } else {
        no b.board[p][col]
        no b.board[otherP][col]
    }

    -- Initializes the turn order
    b.turn = p
    b.turn != otherP
}

-- A board is in a winning state for p if all pits are empty and p has more seeds in their well
pred winning[b: Board, p, otherP: Player] {
    all col: Int | {
        -- all rows are empty
        b.board[p][col] = 0 and b.board[otherP][col] = 0
        -- one player has more marbles in their well than the other player
        b.well[p] > b.well[otherP]
    }
}

-- A board is in a tied state if all pits are empty and both players have the same number of seeds
-- in their wells
pred tied[b: Board, p, otherP: Player] {
    all col: Int | {
        -- all rows are empty
        b.board[p][col] = 0 and b.board[otherP][col] = 0
        -- wells have same amnt of marbles
        b.well[p] = b.well[otherP]
    }
}

-- Helper function that calculates the number of seeds that overflow the player's side + well
fun overflow[pre: Board, player: Player, col: Int] : one Int {
    -- n - (c_o + 1)
    subtract[pre.board[player][col], add[subtract[COLMAX, col], 1]]
}

-- Helper predicate that updates the board based on the player's chosen move
pred moveCases[pre: Board,
               col: Int,
               player: Player,
               otherPlayer: Player,
               post: Board] {
    -- c_s = player's selected pit for this turn = col
    -- n = number of marbles in c_s
    -- c_o = number of columns until player well = COLMAX - col

    -- Case 1: Player only has enough marbles to add to their own pits
    -- Case 1: (c_o >= n) => only all col_p | col_p - c_s <= n get +1
    (subtract[COLMAX, col] >= pre.board[player][col]) => {
        all col_p : Int | (col_p > col) and (subtract[col_p, col] <= pre.board[player][col]) => {
            post.board[player][col_p] = add[pre.board[player][col_p], 1]
            post.board[player][col] = 0
        } else {
            post.board[player][col_p] = pre.board[player][col_p]
        }
    }
    
    -- Case 2: Player's well gets +1 marble
    -- Case 2: c_o = n - 1
    (subtract[COLMAX, col] = subtract[pre.board[player][col], 1]) => {
        post.well[player] = add[pre.well[player], 1]
        all col_p : Int | (col_p > col) and (subtract[col_p, col] <= pre.board[player][col]) => {
            post.board[player][col_p] = add[pre.board[player][col_p], 1]
            post.board[player][col] = 0
        } else {
            post.board[player][col_p] = pre.board[player][col_p]
        }
    }
    
    -- Case 3: There are enough marbles to overflow into the opponent's pits, and potentially loop
    --         back around to the player's pits and well
    -- Case 3: n - (c_o + 1) > 0 && n - (c_o + 1) <= 2 * MAXCOL
    --      => all col_o | [n - (c_o + 1)] - col_o >= 1 get +1
    --      => all col_p | [n - (c_o + 1)] - MAXCOL - col_p >= 1 get +1
    --          => check which player cols need an extra +1
    ((overflow[pre, player, col] > 0) and (overflow[pre, player, col] <= multiply[2, COLMAX])) => {
        -- We check the case where the player can steal marbles from the opponent
        all col_o, col_p: Int | col_p = subtract[COLMAX, col_o] => {
            -- col_p = MAXCOL - col_o for stealing to occur
            (subtract[subtract[overflow[pre, player, col], COLMAX], col_p] = 1) and (pre.board[player][col_p] = 0) => {
                // steal case
                -- Set the opponent's pit to have 0 marbles
                post.board[otherPlayer][col_o] = 0
                -- Check how much overflow there is to add to the well
                (overflow[pre, player, col] = add[multiply[2, COLMAX], 1]) => {
                    -- Add the opponent's marbles to the well + 2
                    post.well[player] = add[add[pre.well[player], pre.board[otherPlayer][col_o]], 2]
                } else {
                    -- Add the opponent's marbles to the well + 1
                    post.well[player] = add[add[pre.well[player], pre.board[otherPlayer][col_o]], 1]
                }
            } else {
                -- Guard: if stealing can't happen then the number of marbles doesn't change
                post.board[otherPlayer][col_o] = pre.board[otherPlayer][col_o]
            }
        } else {
            // non-steal case
            (subtract[overflow[pre, player, col], col_o] >= 1) => {
                -- We add 1 to the opponent's pit
                post.board[otherPlayer][col_o] = add[pre.board[otherPlayer][col_o], 1]
            } else {
                -- Guard: if stealing can't happen then the number of marbles doesn't change
                post.board[otherPlayer][col_o] = pre.board[otherPlayer][col_o]
            }
            -- We check if there's enough overflow to add 2 marbles to the well
            (overflow[pre, player, col] = add[multiply[2, COLMAX], 1]) => {
                post.well[player] = add[pre.well[player], 2]
            }
        }

        -- We check which pits on the player's side the marbles overflow to
        all col_p: Int | {
            -- Case where col_p does get overflow
            subtract[subtract[overflow[pre, player, col], COLMAX], col_p] >= 1 => {
                ((col_p > col) and (subtract[col_p, col] <= pre.board[player][col])) => {
                    -- Case where col_p had 1 marble added from initial distribution
                    post.board[player][col_p] = add[pre.board[player][col_p], 2]
                } else {
                    (col_p = col) => {
                        -- Case where col_p is the original col chosen
                        post.board[player][col_p] = 1
                    } else {
                        -- Case where col_p only gets +1 marble
                        post.board[player][col_p] = add[pre.board[player][col_p], 1]
                    }
                }
            } else {
                -- Case where col_p does not get overflow; guard to ensure nothing changes
                post.board[player][col_p] = pre.board[player][col_p]
            }
        }
    }
    
    -- Case 4: There are enough marbles to potentially loop around the board's pits twice (and add
    --         3 to the player's well)
    -- Case 4: n - (c_o + 1) > 2 * MAXCOL + 1 && n - (c_o + 1) <= 4 * MAXCOL + 1
    --      => all col_o | [n - (c_o + 1)] - (2 * MAXCOL + 1) - col_o >= 1 get +2
    --      => all col_p | [n - (c_o + 1)] - (3 * MAXCOL + 1) - col_p >= 1 get +2
    ((subtract[pre.board[player][col], add[subtract[COLMAX, col], 1]] > add[multiply[2, COLMAX], 1]) and 
    (overflow[pre, player, col] <= add[multiply[4, COLMAX], 1])) => {
        all col_o, col_p: Int | col_p = subtract[COLMAX, col_o] => {
            (subtract[subtract[overflow[pre, player, col], COLMAX], col_p] = 1) and (pre.board[player][col_p] = 0) => {
                // steal case
                post.board[otherPlayer][col_o] = 0
                (overflow[pre, player, col] = add[multiply[4, COLMAX], 2]) => {
                    post.well[player] = add[add[pre.well[player], pre.board[otherPlayer][col_o]], 3]
                } else {
                    post.well[player] = add[pre.well[player], pre.board[otherPlayer][col_o]]
                }
            } else {
                post.board[otherPlayer][col_o] = pre.board[otherPlayer][col_o]
            }
        } else {
            // non-steal case
            subtract[subtract[overflow[pre, player, col], add[multiply[2, COLMAX], 1]], col_o] >= 1 => {
                post.board[otherPlayer][col_o] = add[pre.board[otherPlayer][col_o], 2]
            } else {
                post.board[otherPlayer][col_o] = pre.board[otherPlayer][col_o]
            }
            (overflow[pre, player, col] = add[multiply[4, COLMAX], 2]) => {
                post.well[player] = add[pre.well[player], 3]
            }
        }

        all col_p: Int | {
            subtract[subtract[overflow[pre, player, col], add[multiply[3, COLMAX], 1]], col_p] >= 1 => {
                ((col_p > col) and (subtract[col_p, col] <= pre.board[player][col])) => {
                    post.board[player][col_p] = add[pre.board[player][col_p], 3]
                } else {
                    (col_p = col) => {
                        post.board[player][col_p] = 2
                    } else {
                        post.board[player][col_p] = add[pre.board[player][col_p], 2]
                    }
                }
            } else {
                post.board[player][col_p] = pre.board[player][col_p]
            }
        }
    }
    
    -- Case 5: There are enough marbles to potentially loop around the board's pits thrice
    -- Case 5: n - (c_o + 1) > 4 * MAXCOL + 2 && n - (c_o + 1) <= 6 * MAXCOL + 2
    --      => all col_o | [n - (c_o + 1)] - (4 * MAXCOL + 2) - col_o >= 1 get +3
    --      => all col_p | [n - (c_o + 1)] - (5 * MAXCOL + 2) - col_p >= 1 get +3
    ((subtract[pre.board[player][col], add[subtract[COLMAX, col], 1]] > add[multiply[4, COLMAX], 2]) and 
    (overflow[pre, player, col] <= add[multiply[6, COLMAX], 2])) => {
        all col_o, col_p: Int | col_p = subtract[COLMAX, col_o] => {
            (subtract[subtract[overflow[pre, player, col], COLMAX], col_p] = 1) and (pre.board[player][col_p] = 0) => {
                // steal case
                post.board[otherPlayer][col_o] = 0
                post.well[player] = add[pre.well[player], pre.board[otherPlayer][col_o]]
            } else {
                post.board[otherPlayer][col_o] = pre.board[otherPlayer][col_o]
            }
        } else {
            // non-steal case
            subtract[subtract[overflow[pre, player, col], add[multiply[4, COLMAX], 2]], col_o] >= 1 => {
                post.board[otherPlayer][col_o] = add[pre.board[otherPlayer][col_o], 3]
            } else {
                post.board[otherPlayer][col_o] = pre.board[otherPlayer][col_o]
            }
        }

        all col_p: Int | {
            subtract[subtract[overflow[pre, player, col], add[multiply[5, COLMAX], 2]], col_p] >= 1 => {
                ((col_p > col) and (subtract[col_p, col] <= pre.board[player][col])) => {
                    post.board[player][col_p] = add[pre.board[player][col_p], 4]
                } else {
                    (col_p = col) => {
                        post.board[player][col_p] = 3
                    } else {
                        post.board[player][col_p] = add[pre.board[player][col_p], 3]
                    }
                }
            } else {
                post.board[player][col_p] = pre.board[player][col_p]
            }
        }
    }
}

-- Helper predicate to figure out if player gets another turn or if its the opponent's turn
pred nextTurn[pre: Board,
              col: Int,
              player: Player,
              otherPlayer: Player,
              post: Board] {
    pre.turn = player
    // n = pre.board[player][col]
    // (COLMAX - col) = n - 1 => player gets another turn
    // overflow[pre, player, col] = add[multiply[2, COLMAX], 1] => player's turn
    // overflow[pre, player, col] = add[multiply[4, COLMAX], 2] => player's turn
    (subtract[COLMAX, col] = subtract[pre.board[player][col], 1]) or
    (overflow[pre, player, col] = add[multiply[2, COLMAX], 1]) or
    (overflow[pre, player, col] = add[multiply[4, COLMAX], 2]) => {
        post.turn = player
    } else {
        post.turn = otherPlayer
    }
}

pred move[pre: Board,
          col: Int,
          player: Player,
          otherPlayer: Player,
          post: Board] {
    -- enforce valid moves
    col >= COLMIN
    col <= COLMAX

    -- conditions necessary to make a move
    -- must be the player's turn
    -- must have marbles in selected pit
    pre.turn = player
    pre.board[player][col] > 0

    -- constraint which requires that the number of marbles in each well doesn't
    -- decrease on a turn
    // post.well[player] >= pre.well[player]
    // post.well[otherPlayer] >= pre.well[otherPlayer]
    
    -- prevent winning boards from progressing
    not winning[pre, player, otherPlayer] and not winning[pre, otherPlayer, player]
    
    -- prevent tied boards from progressing
    not tied[pre, player, otherPlayer] and not tied[pre, otherPlayer, player]
    
    all col_o, col_p: Int | pre.board[otherPlayer][col_o] = 0 => {
        -- last move
        post.well[player] = add[pre.board[player][col_p], pre.well[player]]
    } else {
        -- apply move defined by col and set the next turn
        moveCases[pre, col, player, otherPlayer, post]
        nextTurn[pre, col, player, otherPlayer, post]
    }
}

-- If someone is winning or the game is tied, nothing else should change
pred doNothing[pre, post: Board] {
    all p, otherP: Player | {
        winning[pre, p, otherP] or tied[pre, p, otherP]

        all col: Int | {
            pre.board[p][col] = post.board[p][col]
            pre.board[otherP][col] = post.board[otherP][col]
        }
    }
}

one sig Game {
    first: one Board,
    next: pfunc Board -> Board
}

pred trace {
    init[Game.first, P1, P2]
    
    all b: Board | { some Game.next[b] implies {
        (some col: Int | 
            move[b, col, P1, P2, Game.next[b]])
        or
        (doNothing[b, Game.next[b]])
    }}
}

run {
    trace
    allBoardsWellformed
} for 5 Int, 5 Board for { next is linear } // arbitrary amnt of turns
