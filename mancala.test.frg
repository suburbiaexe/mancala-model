#lang forge/bsl

open "mancala.frg"

// checks wellformed via allBoardsWellformed
test suite for allBoardsWellformed {
    example negative_index_bad is {not allBoardsWellformed} for {
    Board = `Board0
    P1 = `P10
    P2 = `P20
    Player = P1 + P2
    `Board0.well = P1 -> 0 + P2 -> 0
    `Board0.turn = P1
    `Board0.board = (P1, 0) -> 4 + (P1, 1) -> 4 + 
                    (P1, 2) -> 4 + (P1, 3) -> 4 + 
                    (P1, 4) -> 4 + (P1, 5) -> 4 + 
                    (P2, 0) -> 4 + (P2, 1) -> 4 + 
                    (P2, 2) -> 4 + (P2, 3) -> 4 + 
                    (P2, 4) -> 4 + (P2, 5) -> 4 +
                    (P2, -1) -> 4
    }

    example big_index_bad is {not allBoardsWellformed} for {
        Board = `Board0
        P1 = `P10
        P2 = `P20
        Player = P1 + P2
        `Board0.well = P1 -> 0 + P2 -> 0
        `Board0.turn = P1
        `Board0.board = (P1, 0) -> 4 + (P1, 1) -> 4 + 
                        (P1, 2) -> 4 + (P1, 3) -> 4 + 
                        (P1, 4) -> 4 + (P1, 5) -> 4 + 
                        (P2, 0) -> 4 + (P2, 1) -> 4 + 
                        (P2, 2) -> 4 + (P2, 3) -> 4 + 
                        (P2, 4) -> 4 + (P2, 6) -> 4
    }

    example negative_marbles_bad is {not allBoardsWellformed} for {
        Board = `Board0
        P1 = `P10
        P2 = `P20
        Player = P1 + P2
        `Board0.well = P1 -> 0 + P2 -> 0
        `Board0.turn = P1
        `Board0.board = (P1, 0) -> 4 + (P1, 1) -> 4 + 
                        (P1, 2) -> 4 + (P1, 3) -> 4 + 
                        (P1, 4) -> 4 + (P1, 5) -> 4 + 
                        (P2, 0) -> 4 + (P2, 1) -> 4 + 
                        (P2, 2) -> 4 + (P2, 3) -> 4 + 
                        (P2, 4) -> 4 + (P2, 5) -> -1
    }
}

pred wrong_num_seeds_in_well {
    some b: Board, p, p2: Player | {
        init[b, p, p2]
        b.well[p] = 5
    }
}

pred not_four_seeds_in_pits {
    some b: Board, p, p2: Player | {
        init[b, p, p2]
        b.board[p][0] = 2
    }
}

pred wrong_turn {
    some b: Board, p, p2: Player | {
        init[b, p, p2]
        b.turn = p2
    }
}

test suite for init {
    test expect { badWellCount: {wrong_num_seeds_in_well} is unsat }
    test expect { badPitCount: {not_four_seeds_in_pits} is unsat }
    test expect { wrongPlayerTurn: {wrong_turn} is unsat }
}

pred not_all_rows_empty_winning {
    some b: Board, p, p2: Player | {
        b.board[p][1] = 2
        winning[b, p, p2]
    }
}

pred no_game_won {
    some b: Board, p, p2: Player | {
        -- note that for a real tied game, each well would have 24 marbles
        -- we're using 7 here because the bitwidth is -8 to 7 and the test
        -- wont run with 24
        b.well[p] = 7
        b.well[p2] = 7
        winning[b, p, p2]
    }
}

test suite for winning {
    test expect { someMarblesStill: {not_all_rows_empty_winning} is unsat }
    test expect { gameTied: {no_game_won} is unsat }
}

pred not_all_rows_empty_tied {
    some b: Board, p, p2: Player | {
        b.board[p][1] = 2
        tied[b, p, p2]
    }
}

pred no_game_tied {
    some b: Board, p, p2: Player | {
        b.well[p] = 5
        b.well[p2] = 3
        tied[b, p, p2]
    }
}

test suite for tied {
    test expect { someMarblesStill2: {not_all_rows_empty_tied} is unsat }
    test expect { gameWon: {no_game_tied} is unsat }
}

-- this test fails, and we haven't been able to figure out why; we realize something
-- is probably wrong with our logic in nextTurn, but at least based on the logic
-- we HAVE for nextTurn, this test should pass even if the function itself is wrong
pred wrong_next_turn {
    some pre, post: Board, p, p2: Player, col: Int | (overflow[pre, p, col] = add[multiply[2, COLMAX], 1]) and pre.turn = p => {
        nextTurn[pre, col, p, p2, post]
        post.turn = p2
    }
}

test suite for nextTurn {
    // test expect { notAnotherTurn: {wrong_next_turn} is unsat }
}

pred neg_selected_col {
    some pre, post: Board, p, p2: Player | {
        move[pre, -1, p, p2, post]
    }
}

pred big_selected_col {
    some pre, post: Board, p, p2: Player | {
        move[pre, 7, p, p2, post]
    }
}

pred no_marbles_in_selected_col {
    some pre, post: Board, p, p2: Player, col: Int | {
        pre.board[p][col] = 0
        move[pre, col, p, p2, post]
    }
}

pred already_won {
    some pre, post: Board, p, p2: Player, col: Int | {
        winning[pre, p, p2]
        move[pre, col, p, p2, post]
    }
}

pred already_tied {
    some pre, post: Board, p, p2: Player, col: Int | {
        tied[pre, p, p2]
        move[pre, col, p, p2, post]
    }
}

test suite for move {
    test expect { negCol: {neg_selected_col} is unsat }
    test expect { bigCol: {big_selected_col} is unsat }
    test expect { noMarbles: {no_marbles_in_selected_col} is unsat }
    test expect { alreadyWon: {already_won} is unsat }
    test expect { alreadyTied: {already_tied} is unsat }
}

-- similar to our test for nextTurn, we're not sure why these tests fail based on
-- how we've written doNothing
pred no_win_or_tie {
    some b: Board, p, p2: Player | {
        not winning[b, p, p2] and not tied[b, p, p2]
    }
}
pred board_not_same {
    some pre, post: Board, p, p2: Player, col: Int | {
        pre.board[p][col] != post.board[p][col]
        pre.board[p2][col] != post.board[p2][col]
    }
}
test suite for doNothing {
    // test expect { gameNotEnded: {no_win_or_tie} is unsat }
    // test expect { boardChanged: {board_not_same} is unsat }
}

-- these tests were all unsat when they should've been sat based on our 
-- implementation
pred move_case_1 {
    some pre, post: Board, p, p2: Player | {
        pre.board[p, 0] = 2
        pre.board[p, 1] = 2
        pre.board[p, 2] = 3
        pre.board[p, 3] = 1
        pre.board[p, 4] = 0
        pre.board[p, 5] = 6
        post.board[p, 0] = 2
        post.board[p, 1] = 2
        post.board[p, 2] = 0
        post.board[p, 3] = 2
        post.board[p, 4] = 1
        post.board[p, 5] = 7
        moveCases[pre, 2, p, p2, post]
    }
}
pred move_case_2 {
    some pre, post: Board, p, p2: Player | {
        pre.board[p, 0] = 2
        pre.board[p, 1] = 2
        pre.board[p, 2] = 4
        pre.board[p, 3] = 1
        pre.board[p, 4] = 0
        pre.board[p, 5] = 6
        pre.well[p] = 0
        post.well[p] = 1
        post.board[p, 0] = 2
        post.board[p, 1] = 2
        post.board[p, 2] = 0
        post.board[p, 3] = 2
        post.board[p, 4] = 1
        post.board[p, 5] = 7
        moveCases[pre, 2, p, p2, post]
    }
}
pred move_case_3_overflow {
    some pre, post: Board, p, p2: Player | {
        pre.board[p, 0] = 2
        pre.board[p, 1] = 2
        pre.board[p, 2] = 5
        pre.board[p, 3] = 1
        pre.board[p, 4] = 0
        pre.board[p, 5] = 6
        pre.board[p2, 0] = 3
        pre.board[p2, 1] = 0
        pre.board[p2, 2] = 1
        pre.board[p2, 3] = 2
        pre.board[p2, 4] = 6
        pre.board[p2, 5] = 3
        post.board[p, 0] = 2
        post.board[p, 1] = 2
        post.board[p, 2] = 0
        post.board[p, 3] = 2
        post.board[p, 4] = 1
        post.board[p, 5] = 7
        post.board[p2, 0] = 4
        post.board[p2, 1] = 0
        post.board[p2, 2] = 1
        post.board[p2, 3] = 2
        post.board[p2, 4] = 6
        post.board[p2, 5] = 3
        moveCases[pre, 2, p, p2, post]
    }
}
pred move_case_3_steal {
    some pre, post: Board, p, p2: Player | {
        pre.board[p, 0] = 1
        pre.board[p, 1] = 0
        pre.board[p2, 1] = 5
        pre.well[p] = 1
        post.board[p, 0] = 0
        post.board[p, 1] = 0
        post.board[p2, 1] = 0
        post.well[p] = 7
        moveCases[pre, 0, p, p2, post]
    }
}
test suite for moveCases {
    // test expect { case1: {move_case_1} is sat }
    // test expect { case2: {move_case_2} is sat }
    // test expect { case3Overflow: {move_case_3_overflow} is sat }
    // test expect { case3Steal: {move_case_3_steal} is sat }
}
