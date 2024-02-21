#lang forge/bsl

abstract sig Player {}
one sig P1, P2 extends Player {}

sig Board {
    well: func Player -> Int,
    -- Player's row -> col -> number of marbles in well
    board: pfunc Player -> Int -> Int
    turn: Player
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
        (b.board[P1][col] = 0) implies {
            add[b.board[P2][col], b.well[P2]]
            b.board[P2][col] = 0
        }

        (b.board[P2][col] = 0) implies {
            add[b.board[P1][col], b.well[P1]]
            b.board[P1][col] = 0
        }
    }

    b.well[p] > b.well[otherP]
}

pred tied[b: Board, p, otherP: Player] {
    all col: Int | {
        -- all rows are empty
        b.board[p][col] = 0 and b.board[otherP][col] = 0
        -- wells have same amnt of marbles
        b.well[p] = b.well[otherP]
    }
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
    b.board[player][col] > 0
    
    -- prevent winning boards from progressing
    not winning[pre, P1, P2] and not winning[pre, P2, P1]
    
    -- prevent tied boards from progressing
    not tied[pre, P1, P2] and not tied[pre, P2, P1]
    
    -- set selected pit to contain 0 marbles
    post.board[player][col] = 0
    -- update the board:
    -- from col+1 to min(COLMAX - col+1, num_marbles), add a marble to each pit
    -- if COLMAX - col+1 < num_marbles, do the same for opponent for 0 to num_marbles - (COLMAX - col+1)
    -- other pits stay the same (number of marbles don't change)
    
    -- num_marbles - (COLMAX - col+1) - 1 > 0
    -- num_marbles - (COLMAX - col+1) - 1 - 5 > 0
    -- num_marbles - (COLMAX - col+1) - 1 - 5 - 6 > 0

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
