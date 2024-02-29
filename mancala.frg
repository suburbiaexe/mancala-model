#lang forge/bsl

abstract sig Player {}
one sig P1, P2 extends Player {}

sig Board {
    well: func Player -> Int,
    -- Player's row -> col -> number of marbles in well
    board: pfunc Player -> Int -> Int,
    turn: one Player
}

fun COLMIN: one Int { 0 }
fun COLMAX: one Int { 5 }

pred wellformed[b: Board, p, otherP: Player] {
    all col: Int | {
        (col < COLMIN or col > COLMAX) implies 
            no b.board[p][col] and no b.board[otherP][col]
        else
            b.board[p][col] >= 0 and
            b.board[otherP][col] >= 0
    }
}

pred allBoardsWellformed { all b : Board | wellformed[b, P1, P2] }

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

    b.turn = p
}

pred winning[b: Board, p, otherP: Player] {
    all col: Int | {
        -- all rows are empty
        b.board[p][col] = 0 and b.board[otherP][col] = 0
        -- one player has more marbles in their well than the other player
        b.well[p] > b.well[otherP]
    }
}

pred tied[b: Board, p, otherP: Player] {
    all col: Int | {
        -- all rows are empty
        b.board[p][col] = 0 and b.board[otherP][col] = 0
        -- wells have same amnt of marbles
        b.well[p] = b.well[otherP]
    }
}

fun overflow[pre: Board, player: Player, col: Int] : one Int {
    -- n - (c_o + 1)
    subtract[pre.board[player][col], add[subtract[COLMAX, col], 1]]
}

pred addToWell[pre: Board,
               col: Int,
               player: Player,
               post: Board,
               numToAdd: Int] {
    -- n - (c_o + 1) = numToAdd * COLMAX + 1
    overflow[pre, player, col] = add[multiply[numToAdd, COLMAX], 1] => {
        post.well[player] = add[pre.well[player], numToAdd]
    }
}

pred moveCases[pre: Board,
               col: Int,
               player: Player,
               otherPlayer: Player,
               post: Board] {
    -- update the board:    
    -- n = number of marbles in selected pit (c_s = col)
    -- c_o = number of columns until player well
    -- c_o = COLMAX - col
    -- Case 1: (c_o >= n) => only all col_p | col_p - c_s <= n get +1
    (subtract[COLMAX, col] >= pre.board[player][col]) => {
        all col_p : Int | (col_p > col) and (subtract[col_p, col] <= pre.board[player][col]) => {
            post.board[player][col_p] = add[pre.board[player][col_p], 1]
            post.board[player][col] = 0
        } else {
            post.board[player][col_p] = pre.board[player][col_p]
        }
    }
    
    -- Case 2: c_o = n - 1 => player well gets +1
    (subtract[COLMAX, col] = subtract[pre.board[player][col], 1]) => {
        post.well[player] = add[pre.well[player], 1]
        all col_p : Int | (col_p > col) and (subtract[col_p, col] <= pre.board[player][col]) => {
            post.board[player][col_p] = add[pre.board[player][col_p], 1]
            post.board[player][col] = 0
        } else {
            post.board[player][col_p] = pre.board[player][col_p]
        }
    }
    
    -- Case 3: n - (c_o + 1) > 0 && n - (c_o + 1) <= 2 * MAXCOL
    --      => all col_o | [n - (c_o + 1)] - col_o >= 1 get +1
    --      => all col_p | [n - (c_o + 1)] - MAXCOL - col_p >= 1 get +1
    --          => check which player cols need an extra +1
    ((overflow[pre, player, col] > 0) and 
    (overflow[pre, player, col] <= multiply[2, COLMAX])) => {
        all col_o, col_p: Int | col_p = subtract[COLMAX, col_o] => {
            -- col_p = MAXCOL - col_o
            -- player[col_p] = 0 and [n - (c_o + 1)] - MAXCOL - col_p = 1 =>
            -- post.board[player][col_o] = 0 and update the players' well
            (subtract[subtract[overflow[pre, player, col], COLMAX], col_p] = 1) and (pre.board[player][col_p] = 0) => {
                // steal case
                post.board[otherPlayer][col_o] = 0
                (overflow[pre, player, col] = add[multiply[2, COLMAX], 1]) => {
                    post.well[player] = add[add[pre.well[player], pre.board[otherPlayer][col_o]], 2]
                } else {
                    post.well[player] = add[pre.well[player], pre.board[otherPlayer][col_o]]
                }
            } else {
                post.board[otherPlayer][col_o] = pre.board[otherPlayer][col_o]
            }
        } else {
            // non-steal case
            (subtract[overflow[pre, player, col], col_o] >= 1) => {
                post.board[otherPlayer][col_o] = add[pre.board[otherPlayer][col_o], 1]
            } else {
                post.board[otherPlayer][col_o] = pre.board[otherPlayer][col_o]
            }
            (overflow[pre, player, col] = add[multiply[2, COLMAX], 1]) => {
                post.well[player] = add[pre.well[player], 2]
            }
        }

        all col_p: Int | {
            subtract[subtract[overflow[pre, player, col], COLMAX], col_p] >= 1 => {
                ((col_p > col) and (subtract[col_p, col] <= pre.board[player][col])) => {
                    post.board[player][col_p] = add[pre.board[player][col_p], 2]
                } else {
                    (col_p = col) => {
                        post.board[player][col_p] = 1
                    } else {
                        post.board[player][col_p] = add[pre.board[player][col_p], 1]
                    }
                }
            } else {
                post.board[player][col_p] = pre.board[player][col_p]
            }
        }
    }
    
    // -- Case 3.5: n - (c_o + 1) == 2 * MAXCOL + 1 => player well gets +2
    // (overflow[pre, player, col] = add[multiply[2, COLMAX], 1]) => {
    //     post.well[player] = add[pre.well[player], 2]
    // }
    
    -- Case 4: n - (c_o + 1) > 2 * MAXCOL + 1 && n - (c_o + 1) <= 4 * MAXCOL + 1
    --      => all col_o | [n - (c_o + 1)] - (2 * MAXCOL + 1) - col_o >= 1 get +2
    --      => all col_p | [n - (c_o + 1)] - (3 * MAXCOL + 1) - col_p >= 1 get +2
    // ((subtract[pre.board[player][col], add[subtract[COLMAX, col], 1]] > add[multiply[2, COLMAX], 1]) and 
    // (overflow[pre, player, col] <= add[multiply[4, COLMAX], 1])) => {
    //     all col_o, col_p: Int | col_p = subtract[COLMAX, col_o] => {
    //         (subtract[subtract[overflow[pre, player, col], COLMAX], col_p] = 1) and (pre.board[player][col_p] = 0) => {
    //             // steal case
    //             post.board[otherPlayer][col_o] = 0
    //             (overflow[pre, player, col] = add[multiply[4, COLMAX], 2]) => {
    //                 post.well[player] = add[add[pre.well[player], pre.board[otherPlayer][col_o]], 3]
    //             } else {
    //                 post.well[player] = add[pre.well[player], pre.board[otherPlayer][col_o]]
    //             }
    //         } else {
    //             post.board[otherPlayer][col_o] = pre.board[otherPlayer][col_o]
    //         }
    //     } else {
    //         // non-steal case
    //         subtract[subtract[overflow[pre, player, col], add[multiply[2, COLMAX], 1]], col_o] >= 1 => {
    //             post.board[otherPlayer][col_o] = add[pre.board[otherPlayer][col_o], 2]
    //         } else {
    //             post.board[otherPlayer][col_o] = pre.board[otherPlayer][col_o]
    //         }
    //         (overflow[pre, player, col] = add[multiply[4, COLMAX], 2]) => {
    //             post.well[player] = add[pre.well[player], 3]
    //         }
    //     }

    //     all col_p: Int | {
    //         subtract[subtract[overflow[pre, player, col], add[multiply[3, COLMAX], 1]], col_p] >= 1 => {
    //             ((col_p > col) and (subtract[col_p, col] <= pre.board[player][col])) => {
    //                 post.board[player][col_p] = add[pre.board[player][col_p], 3]
    //             } else {
    //                 (col_p = col) => {
    //                     post.board[player][col_p] = 2
    //                 } else {
    //                     post.board[player][col_p] = add[pre.board[player][col_p], 2]
    //                 }
    //             }
    //         } else {
    //             post.board[player][col_p] = pre.board[player][col_p]
    //         }
    //     }
    // }
    
    // -- Case 4.5: n - (c_o + 1) == 4 * MAXCOL + 2 => player well gets +3
    // // (overflow[pre, player, col] = add[multiply[4, COLMAX], 2]) => {
    // //     post.well[player] = add[pre.well[player], 3]
    // // }
    
    // -- Case 5: n - (c_o + 1) > 4 * MAXCOL + 2 && n - (c_o + 1) <= 6 * MAXCOL + 2
    // --      => all col_o | [n - (c_o + 1)] - (4 * MAXCOL + 2) - col_o >= 1 get +3
    // --      => all col_p | [n - (c_o + 1)] - (5 * MAXCOL + 2) - col_p >= 1 get +3
    // ((subtract[pre.board[player][col], add[subtract[COLMAX, col], 1]] > add[multiply[4, COLMAX], 2]) and 
    // (overflow[pre, player, col] <= add[multiply[6, COLMAX], 2])) => {
    //     all col_o, col_p: Int | col_p = subtract[COLMAX, col_o] => {
    //         (subtract[subtract[overflow[pre, player, col], COLMAX], col_p] = 1) and (pre.board[player][col_p] = 0) => {
    //             // steal case
    //             post.board[otherPlayer][col_o] = 0
    //             post.well[player] = add[pre.well[player], pre.board[otherPlayer][col_o]]
    //         } else {
    //             post.board[otherPlayer][col_o] = pre.board[otherPlayer][col_o]
    //         }
    //     } else {
    //         // non-steal case
    //         subtract[subtract[overflow[pre, player, col], add[multiply[4, COLMAX], 2]], col_o] >= 1 => {
    //             post.board[otherPlayer][col_o] = add[pre.board[otherPlayer][col_o], 3]
    //         } else {
    //             post.board[otherPlayer][col_o] = pre.board[otherPlayer][col_o]
    //         }
    //     }

    //     all col_p: Int | {
    //         subtract[subtract[overflow[pre, player, col], add[multiply[5, COLMAX], 2]], col_p] >= 1 => {
    //             ((col_p > col) and (subtract[col_p, col] <= pre.board[player][col])) => {
    //                 post.board[player][col_p] = add[pre.board[player][col_p], 4]
    //             } else {
    //                 (col_p = col) => {
    //                     post.board[player][col_p] = 3
    //                 } else {
    //                     post.board[player][col_p] = add[pre.board[player][col_p], 3]
    //                 }
    //             }
    //         } else {
    //             post.board[player][col_p] = pre.board[player][col_p]
    //         }
    //     }
    // }
}

pred nextTurn[pre: Board,
              col: Int,
              player: Player,
              otherPlayer: Player,
              post: Board] {
    // n = pre.board[player][col]
    // (COLMAX - col) = n - 1 => player's turn
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
    
    -- prevent winning boards from progressing
    not winning[pre, player, otherPlayer] and not winning[pre, otherPlayer, player]
    
    -- prevent tied boards from progressing
    not tied[pre, player, otherPlayer] and not tied[pre, otherPlayer, player]
    
    all col_o, col_p: Int | pre.board[otherPlayer][col_o] = 0 => {
        // last move
        post.well[player] = add[pre.board[player][col_p], pre.well[player]]
    } else {
        moveCases[pre, col, player, otherPlayer, post]
        nextTurn[pre, col, player, otherPlayer, post]
    }
}

pred doNothing[pre, post: Board] {
    some p, otherP: Player | {
        winning[pre, p, otherP] or tied[pre, p, otherP]

        all col: Int | {
            pre.board[p][col] = post.board[p][col]
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
} for 5 Int, 2 Board for { next is linear } // arbitrary amnt of turns
