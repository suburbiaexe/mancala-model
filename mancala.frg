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

pred wellformed[b: Board] {
    all col: Int | {
        (col < COLMIN or col > COLMAX) implies 
            no b.board[P1][col] and no b.board[P2][col]
        else
            b.board[P1][col] >= 0 and
            b.board[P2][col] >= 0
    }
}

pred allBoardsWellformed { all b : Board | wellformed[b] }

pred init[b: Board] {
    b.well[P1] = 0
    b.well[P2] = 0

    all col: Int | {
        b.board[P1][col] = 4
        b.board[P2][col] = 4
    }

    b.turn = P1
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

pred addToWell[pre: Board,
               col: Int,
               player: Player,
               post: Board,
               numToAdd: Int] {
    subtract[pre.board[player][col], add[subtract[COLMAX, col], 1]] = add[multiply[numToAdd, COLMAX], 1] => {
        post.well[player] = add[pre.well[player], numToAdd]
    }
}

fun overflow[pre: Board, player: Player, col: Int] : one Int {
    subtract[pre.board[player][col], add[subtract[COLMAX, col], 1]]
}

pred move[pre: Board,
          col: Int,
          player: Player,
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
    not winning[pre, P1, P2] and not winning[pre, P2, P1]
    
    -- prevent tied boards from progressing
    not tied[pre, P1, P2] and not tied[pre, P2, P1]
    
    -- set selected pit to contain 0 marbles
    post.board[player][col] = 0
    
    -- TODO: check case where one player's column is completely empty (win case)
    
    -- update the board:    
    -- n = number of marbles in selected pit (c_s = col)
    -- c_o = number of columns until player well
    -- c_o = COLMAX - col
    -- Case 1: c_o > n => all col_p | col_p - c_s <= n get +1
    (subtract[COLMAX, col] > pre.board[player][col]) => {
        all col_p : Int | subtract[col_p, col] <= pre.board[player][col] => {
            post.board[player][col_p] = add[pre.board[player][col_p], 1]
        }
    }
    
    -- Case 2: c_o = n - 1 => player well gets +1
    (subtract[COLMAX, col] = subtract[pre.board[player][col], 1]) => {
        post.well[player] = add[pre.well[player], 1]
    }
    
    -- Case 3: n - (c_o + 1) > 0 && n - (c_o + 1) <= 2 * MAXCOL
    --      => all col_o | [n - (c_o + 1)] - col_o >= 1 get +1
    --      => all col_p | [n - (c_o + 1)] - MAXCOL - col_p >= 1 get +1
    --          => check which player cols need an extra +1
    ((overflow[pre, player, col] > 0) and 
    (overflow[pre, player, col] <= multiply[2, COLMAX])) => {
        all col_o: Int | {
            subtract[overflow[pre, player, col], col_o] >= 1 => {
                post.board[player][col_o] = add[pre.board[player][col_o], 1]
            }

            -- col_p = MAXCOL - col_o
            -- player[col_p] = 0 and [n - (c_o + 1)] - MAXCOL - col_p = 1 =>
            -- post.board[player][col_o] = 0 and update the players' well
        }

        all col_p: Int | {
            subtract[subtract[overflow[pre, player, col], COLMAX], col_p] >= 1 => {
                post.board[player][col_p] = add[pre.board[player][col_p], 1]
            }

            -- if num seeds in col_p = 0 and [n - (c_o + 1)] - MAXCOL - col_p = 1 =>
            -- set opponent[col_p] = 0 and update player's well
            (pre.board[player][col_p] = 0 and subtract[subtract[overflow[pre, player, col], COLMAX], col_p] >= 1)
        }
    }
    
    -- Case 3.5: n - (c_o + 1) == 2 * MAXCOL + 1 => player well gets +2
    (overflow[pre, player, col] = add[multiply[2, COLMAX], 1]) => {
        post.well[player] = add[pre.well[player], 2]
    }
    
    -- Case 4: n - (c_o + 1) > 2 * MAXCOL + 1 && n - (c_o + 1) <= 4 * MAXCOL + 1
    --      => all col_o | [n - (c_o + 1)] - (2 * MAXCOL + 1) - col_o >= 1 get +2
    --      => all col_p | [n - (c_o + 1)] - (3 * MAXCOL + 1) - col_p >= 1 get +2
    ((subtract[pre.board[player][col], add[subtract[COLMAX, col], 1]] > add[multiply[2, COLMAX], 1]) and 
    (overflow[pre, player, col] <= add[multiply[4, COLMAX], 1])) => {
        all col_o: Int | {
            subtract[subtract[overflow[pre, player, col], add[multiply[2, COLMAX], 1]], col_o] >= 1 => {
                post.board[player][col_o] = add[pre.board[player][col_o], 2]
            }
        }

        all col_p: Int | {
            subtract[subtract[overflow[pre, player, col], add[multiply[3, COLMAX], 1]], col_p] >= 1 => {
                post.board[player][col_p] = add[pre.board[player][col_p], 2]
            }

            -- if num seeds in col_p = 0 and [n - (c_o + 1)] - (3 * MAXCOL + 1) - col_p = 1 =>
            -- steal from opponent's col_p 
            // (pre.board[player][col_p] = 0 and )
        }
    }
    
    -- Case 4.5: n - (c_o + 1) == 4 * MAXCOL + 2 => player well gets +3
    (overflow[pre, player, col] = add[multiply[4, COLMAX], 2]) => {
        post.well[player] = add[pre.well[player], 3]
    }
    
    -- Case 5: n - (c_o + 1) > 4 * MAXCOL + 2 && n - (c_o + 1) <= 6 * MAXCOL + 2
    --      => all col_o | [n - (c_o + 1)] - (4 * MAXCOL + 2) - col_o >= 1 get +3
    --      => all col_p | [n - (c_o + 1)] - (5 * MAXCOL + 2) - col_p >= 1 get +3
    ((subtract[pre.board[player][col], add[subtract[COLMAX, col], 1]] > add[multiply[4, COLMAX], 2]) and 
    (overflow[pre, player, col] <= add[multiply[6, COLMAX], 2])) => {
        all col_o: Int | {
            subtract[subtract[overflow[pre, player, col], add[multiply[4, COLMAX], 2]], col_o] >= 1 => {
                post.board[player][col_o] = add[pre.board[player][col_o], 3]
            }
        }

        all col_p: Int | {
            subtract[subtract[overflow[pre, player, col], add[multiply[5, COLMAX], 2]], col_p] >= 1 => {
                post.board[player][col_p] = add[pre.board[player][col_p], 3]
            }

            -- if num seeds in col_p = 0 and [n - (c_o + 1)] - (5 * MAXCOL + 2) - col_p = 1 =>
            -- steal from opponent's col_p 
        }
    }

    -- for all cols, if col1 > col and col1 - col <= num_marbles, add 1 marble to col1
    all col1: Int | (col1 > col) and (subtract[col1, col] <= pre.board[player][col]) implies {
        post.board[player][col1] = add[pre.board[player][col1], 1]
    }
    -- if COLMAX - col+1 < num_marbles, add 1 to player's well
    (subtract[COLMAX, add[col, 1]] < pre.board[player][col]) implies
        post.well[player] = add[pre.well[player], 1]
    -- if COLMAX - col+1 < num_marbles - 1

    -- if nothing changes on opposing player's side, then you know that the move only
    -- could've landed in one of your pits or your well -> only need to check 2 cases?
    -- we also do need to check the case when you land in a pit of yours that's empty, but
    -- is across from opposing player's pit which has marbles, and we get to capture their marbles
}

pred doNothing[pre, post: Board] {
    some p, otherP: Player | {
        winning[pre, p, otherP]

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
    init[Game.first]
    
    all b: Board | { some Game.next[b] implies {
        (some col: Int, p: Player | 
            move[b, col, p, Game.next[b]])
        or
        doNothing[b, Game.next[b]]
    }}
}
run {
    trace
    allBoardsWellformed
} for 10 Board for { next is linear } // arbitrary amnt of turns
