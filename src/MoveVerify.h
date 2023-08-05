//
// Created by evcmo on 7/4/2021.
//

#pragma once
#ifndef HOMURA_MOVEVERIFY_H
#define HOMURA_MOVEVERIFY_H

#include "ChaosMagic.h"
#include "Board.h"
#include "Move.h"
#include <cassert>
#include <algorithm>
#include <mutex>

namespace Homura {

    /**
     * TODO: MOVE BACK TO ANON NAMESPACE IN CPP !!!
     *
     * A function to find attackers on the fly.
     *
     * @tparam A    the alliance of the piece
     *              on the square under attack
     * @tparam PT   the piece type
     * @param board the current game board
     * @param sq    the square under attack
     */
    template<Alliance A, PieceType PT> [[nodiscard]]
    constexpr uint64_t attacksOn(Board* const board, const int sq) {
        static_assert(A == White || A == Black);
        static_assert(PT >= Pawn && PT <= NullPT);

        constexpr const Alliance us = A, them = ~us;

        // Initialize constants.
        const uint64_t theirQueens = board->getPieces<them, Queen>(),
                       target      = PT == NullPT? 0: board->getPieces<us, PT>(),
                       allPieces   = board->getAllPieces() & ~target;

        // Calculate and return a bitboard representing all attackers.
        return (attackBoard<Rook>(allPieces, sq)   &
               (board->getPieces<them, Rook>()   | theirQueens)) |
               (attackBoard<Bishop>(allPieces, sq) &
               (board->getPieces<them, Bishop>() | theirQueens)) |
               (SquareToKnightAttacks[sq]   & board->getPieces<them, Knight>()) |
               (SquareToPawnAttacks[us][sq] & board->getPieces<them, Pawn>())   |
               (SquareToKingAttacks[sq]     & board->getPieces<them, King>());
    }

    /**
     * A function to calculate check for our king given a
     * bitboard representing the pieces that attack its
     * square.
     *
     * @param checkBoard a bitboard of all pieces that attack
     * our king
     * @return whether or not our king is in check
     */
    constexpr CheckType
    calculateCheck(uint64_t checkBoard) {
        return !checkBoard ? None:
               (checkBoard & (checkBoard - 1)) ?
               DoubleCheck: Check;
    }

    namespace MoveVerifier {
        bool verify(Board* b, Move m, PieceType pt);
    }
}


#endif //HOMURA_MOVEVERIFY_H
