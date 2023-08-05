//
// Created by evcmo on 7/4/2021.
//

#include "MoveMake.h"

namespace Homura {
    namespace {

        /**
         * A function to determine whether all squares represented
         * by high bits in the given bitboard are safe to travel to.
         *
         * @tparam A    the alliance to consider
         * @param board the current game board
         * @param d     the bitboard to check for safe squares
         * @return      whether or not all squares represented
         *              by high bits in the given bitboard are
         *              safe to travel to
         */
        template <Alliance A> [[nodiscard]]
        inline bool safeSquares(Board* const board,
                                const uint64_t destinations) {
            static_assert(A == White || A == Black);
            for (uint64_t d = destinations; d; d &= d - 1)
                if (attacksOn<A, NullPT>(board, bitScanFwd(d)))
                    return false;
            return true;
        }

        /**
         * A function to generate this Player'x pawn moves.
         *
         * ToDo: add promotion capability.
         *
         * @tparam A        the alliance
         * @tparam FT       the filter type
         * @param board     the board to use
         * @param checkPath the check mask to use in the
         *                  case of check or double check
         * @param kingGuard a bitboard representing the
         *                  pieces that block sliding
         *                  attacks on the king
         *                  for the given alliance
         * @param moves     a pointer to a list to populate
         *                  with moves
         * @return          a pointer to the next empty
         *                  index in the array that holds
         *                  the moves list
         */
        template <Alliance A>
        bool verifyPawnMove(Board* const board,
                            const uint64_t checkPath,
                            const uint64_t kingGuard,
                            const int kingSquare,
                            Move move) {
            static_assert(A == White || A == Black);

            constexpr const Alliance us = A, them = ~us;

            // Determine defaults.
            constexpr const Defaults* const x = defaults<us>();

            // Initialize constants.
            const uint64_t enemies         = board->getPieces<them>() & checkPath,
                           allPieces       = board->getAllPieces(),
                           emptySquares    = ~allPieces,
                           pawns           = board->getPieces<us, Pawn>(),
                           king            = board->getPieces<us, King>(),
                           freePawns       = pawns & ~kingGuard,
                           pinnedPawns     = pawns & kingGuard,
                           freeLowPawns    = freePawns & ~x->prePromotionMask,
                           freeHighPawns   = freePawns & x->prePromotionMask,
                           pinnedLowPawns  = pinnedPawns & ~x->prePromotionMask,
                           pinnedHighPawns = pinnedPawns & x->prePromotionMask;

            const int      origin           = move.origin(),
                           destination      = move.destination();
            const uint64_t originBoard      = SquareToBitBoard[origin],
                           destinationBoard = SquareToBitBoard[destination];

            if(!(originBoard & pawns)) return false;
            
            // Generate single and double pushes for free low pawns.
            // All pseudo-legal, passive targets one square ahead.
            uint64_t p1 = shift<x->up>(freeLowPawns) & emptySquares;

            // All pseudo-legal, passive targets two squares ahead.
            uint64_t p2 = shift<x->up>(p1 & x->pawnJumpSquares)
                & emptySquares;

            // Intersect the pushes with the current checkPath. The
            // push targets are now legal.
            p1 &= checkPath;
            p2 &= checkPath;

            if(destinationBoard & p1 || destinationBoard & p2)
                return true;


            // Generate left and right attack moves for free low pawns.
            // All legal aggressive targets one square ahead and
            // to the right.
            uint64_t ar =
                shift<x->upRight>(freeLowPawns & x->notRightCol)
                    & enemies;

            // All legal aggressive targets one square ahead and
            // to the left.
            uint64_t al =
                shift<x->upLeft>(freeLowPawns & x->notLeftCol)
                    & enemies;

            if(destinationBoard & ar || destinationBoard & al)
                return true;

            // Generate single and double pushes for pinned low pawns,
            // if any.
            // Generate left and right attack moves for pinned low pawns,
            // if any.
            if (pinnedLowPawns) {

                // All pseudo-legal, passive targets one square ahead.
                uint64_t p1 = shift<x->up>(pinnedLowPawns) & emptySquares;

                // All pseudo-legal, passive targets two squares ahead.
                uint64_t p2 = shift<x->up>(p1 & x->pawnJumpSquares)
                                & emptySquares;

                // Intersect the pushes with the current checkPath.
                p1 &= checkPath;
                p2 &= checkPath;
                p1 &= destinationBoard;
                p2 &= destinationBoard;

                if ((rayBoard(kingSquare, origin) & p1 &
                    (uint64_t) -(int64_t) p1))
                    return true;

                if ((rayBoard(kingSquare, origin) & p2 &
                    (uint64_t) -(int64_t) p2))
                    return true;

                // All pseudo-legal aggressive targets one square ahead
                // and to the right.
                uint64_t ar =
                    shift<x->upRight>(pinnedLowPawns & x->notRightCol)
                        & enemies;

                // All pseudo-legal aggressive targets one square ahead
                // and to the left.
                uint64_t al =
                    shift<x->upLeft>(pinnedLowPawns & x->notLeftCol)
                        & enemies;

                ar &= destinationBoard;
                al &= destinationBoard;

                if ((rayBoard(kingSquare, origin) & ar &
                    (uint64_t) -(int64_t) ar))
                    return true;
                
                if ((rayBoard(kingSquare, origin) & al &
                    (uint64_t) -(int64_t) al))
                    return true;
            }

            // Generate promotion moves for free high pawns.
            if (freeHighPawns) {
                // Calculate single promotion push.
                // All legal promotion targets one square ahead.
                uint64_t p1 = shift<x->up>(freeHighPawns) &
                                emptySquares & checkPath;

                if(destinationBoard & p1)
                    return true;

                // All legal aggressive targets one square ahead
                // and to the right.
                uint64_t ar =
                    shift<x->upRight>(freeHighPawns & x->notRightCol)
                        & enemies;

                // All legal aggressive targets one square ahead
                // and to the left.
                uint64_t al =
                    shift<x->upLeft >(freeHighPawns & x->notLeftCol)
                        & enemies;

                if(destinationBoard & ar || destinationBoard & al)
                    return true;
            }

            // Generate promotion moves for pinned high pawns.
            if (pinnedHighPawns) {
                // Calculate single promotion push for pinned pawns.
                // All pseudo-legal promotion targets one square ahead.
                uint64_t p1 =
                        shift<x->up>(pinnedHighPawns) & emptySquares & checkPath;

                p1 &= destinationBoard;

                if((rayBoard(kingSquare, origin) &
                   p1 & (uint64_t) - (int64_t)p1))
                   return true;
                   
                // All pseudo-legal aggressive targets one square ahead
                // and to the right.
                uint64_t ar =
                    shift<x->upRight>(pinnedHighPawns & x->notRightCol)
                        & enemies;

                // All pseudo-legal aggressive targets one square ahead
                // and to the left.
                uint64_t al =
                    shift<x->upLeft >(pinnedHighPawns & x->notLeftCol)
                        & enemies;

                ar &= destinationBoard;
                al &= destinationBoard;

                if((rayBoard(kingSquare, origin) &
                   ar & (uint64_t) - (int64_t)ar))
                    return true;

                if((rayBoard(kingSquare, origin) &
                   al & (uint64_t) - (int64_t)al))
                    return true;
            }

            // Find the en passant square, if any.
            const int enPassantSquare = board->getEpSquare();

            // If the en passant square is set, continue.
            if (enPassantSquare == NullSQ) return false;

            // The en passant pawn square board.
            const uint64_t eppBoard  = SquareToBitBoard[enPassantSquare];

            // The en passant destination board.
            const uint64_t destBoard = shift<x->up>(eppBoard);
            
            if (!(destinationBoard & destBoard)) return false;

            // If we are in single check and the destination
            // doesn't block... and if the en passant pawn is
            // not the king's attacker... Don't generate an en
            // passant move.
            if (!(destBoard & checkPath) &&
                !(eppBoard  & SquareToPawnAttacks[us][kingSquare]))
                    return false;

            // Calculate the pass mask.
            const uint64_t passMask =
                    shift<x->right>(eppBoard & x->notRightCol) |
                    shift<x->left >(eppBoard & x->notLeftCol );

            // Calculate free passing pawns.
            const uint64_t freePasses   = passMask & freeLowPawns;

            // Calculate pinned passing pawns.
            const uint64_t pinnedPasses = passMask & pinnedLowPawns;

            // If there is a passing pawn, generate legal
            // en passant moves.
            if (!(freePasses || pinnedPasses))
                return false;

            // If the king is on the en passant rank then
            // a horizontal en passant discovered check is possible.
            if (king & x->enPassantRank) {
                // Find the snipers on the en passant rank.
                const uint64_t snipers =
                    (board->getPieces<them, Queen>() |
                     board->getPieces<them, Rook>()) &
                     x->enPassantRank;

                // Check to see if the en passant pawn
                // (and attacking pawn) are between any of
                // the snipers and the king square. If so,
                // check to see if these two pawns are the
                // ONLY blocking pieces between the sniper
                // and the king square.
                // If this is the case, then any en passant move
                // will leave our king in check. We are done
                // generating pawn moves.
                for (uint64_t s = snipers; s; s &= s - 1) {
                    const uint64_t path =
                        pathBoard(bitScanFwd(s), kingSquare);
                    if (eppBoard & path) {
                        const uint64_t b = allPieces &
                            ~snipers & path, c = b & (b - 1);
                        if (b && c && !(c & (c - 1)))
                            return false;
                    }
                }

            // If the king square has a path to the en Passant
            // square but isn't on the rank of the en passant
            // pawn, en en passant discovered check is still
            // possible.
            } else if (pathBoard(kingSquare, enPassantSquare)) {

                const uint64_t diagonalSnipers =
                    (attackBoard<Bishop>(0, kingSquare) &
                    (board->getPieces<them, Bishop>() |
                     board->getPieces<them, Queen>()));

                // Check to see if the en passant pawn
                // is between any of the snipers and the king
                // square. If so, check to see if this pawn is
                // the ONLY blocking piece between the sniper
                // and the king square.
                // If this is the case, then any en passant move
                // will leave our king in check. We are done
                // generating pawn moves.
                for (uint64_t s = diagonalSnipers; s; s &= s - 1) {
                    const uint64_t path =
                            pathBoard(bitScanFwd(s), kingSquare);
                    if (eppBoard & path) {
                        const uint64_t b = allPieces & path;
                        if (b && !(b & (b - 1)))
                            return false;
                    }
                }
            }

            if(freePasses & originBoard)
                return true;

            if((pinnedPasses & originBoard) &&
               (destBoard & rayBoard(kingSquare, origin)))
                return true;

            return false;
        }

        /**
         * A function to generate the moves for a given piece
         * type.
         *
         * @tparam A        the alliance to consider
         * @tparam PT       the piece type to consider
         * @param board     the current game board
         * @param kingGuard the king guard for the given
         *                  alliance
         * @param filter    the filter mask to use
         * @param moves     a pointer to a list to
         *                  populate with moves
         * @return          a pointer to the next empty
         *                  index in the array that holds
         *                  the moves list
         */
        template<Alliance A, PieceType PT>
        bool verifyMove(Board* const board,
                         const uint64_t kingGuard,
                         const uint64_t filter,
                         const int kingSquare,
                         Move move) {
            static_assert(A == White || A == Black);
            static_assert(PT >= Rook && PT <= Queen);

            constexpr const Alliance us = A;

            // Initialize constants.
            const uint64_t pieceBoard = board->getPieces<us, PT>(),
                           freePieces = pieceBoard & ~kingGuard,
                           allPieces  = board->getAllPieces(),
                           // All pieces pinned between the king and an
                           // attacker.    
                           pinnedPieces = pieceBoard & kingGuard;

            const int      origin           = move.origin(),
                           destination      = move.destination();
            const uint64_t originBoard      = SquareToBitBoard[origin],
                           destinationBoard = SquareToBitBoard[destination];

            if(freePieces & originBoard) {

                // Look up the attack board using the origin
                // square and intersect with the filter.
                uint64_t ab = attackBoard<PT>(allPieces, origin)
                    & filter;

                return ab & destinationBoard;
            } 
            
            if(pinnedPieces & originBoard) {
                if constexpr (PT == Knight)
                    return false;

                // Lookup the attack board and intersect with
                // the filter and the pinning ray.
                uint64_t ab =
                    attackBoard<PT>(allPieces, origin)
                        & filter & rayBoard(kingSquare, origin);
                
                return ab & destinationBoard; 
            } 
            
            return false;
        }

        /**
         * A function to generate moves for every piece type.
         *
         * @tparam A    the alliance to consider
         * @tparam FT   the filter type
         * @param board the current game board
         * @param moves a pointer to the list to populate
         */
        template <Alliance A>
        bool verifyMove(Board* const board, Move move, PieceType pt) {
            static_assert(A == White || A == Black);
            if(move == NullMove) return false;
            if(pt == NullPT) return false;

            constexpr const Alliance us = A, them = ~us;

            // Initialize constants.
            const uint64_t allPieces     = board->getAllPieces(),
                           ourPieces     = board->getPieces<us>(),
                           theirPieces   = board->getPieces<them>(),
                           partialFilter = ~ourPieces,
                           king          = board->getPieces<us, King>();

            // Get the board defaults for our alliance.
            constexpr const Defaults* const x = defaults<us>();

            // Find the king square.
            const int ksq = bitScanFwd(king);

            // Find all pieces that attack our king.
            const uint64_t checkBoard = attacksOn<us, King>(board, ksq);

            // Calculate the check type for our king.
            const CheckType checkType = calculateCheck(checkBoard);

            if(pt == King) {
                // Test king move.
                const int      origin           = move.origin(),
                               destination      = move.destination();
                const uint64_t originBoard      = SquareToBitBoard[origin],
                               destinationBoard = SquareToBitBoard[destination];

                if(ksq != origin) return false;

                uint64_t d = SquareToKingAttacks[ksq];

                if((d & destinationBoard) && 
                    !attacksOn<us, King>(board, destination))
                    return true;

                if (checkType != None)
                    return false;

                if(ksq == origin) {
                    if(x->kingSideDestination == destination &&
                        !(x->kingSideMask & allPieces) &&
                        board->hasCastlingRights<us, KingSide>() &&
                        safeSquares<us>(board, x->kingSideCastlePath))
                        return true;

                    if(x->queenSideDestination == destination &&
                        !(x->queenSideMask & allPieces) &&
                        board->hasCastlingRights<us, QueenSide>() &&
                        safeSquares<us>(board, x->queenSideCastlePath))
                        return true;
                }

                return false;
            }

            if (checkType == DoubleCheck) return false;

            uint64_t blockers = 0;
            const uint64_t theirQueens =
                    board->getPieces<them, Queen>();

            // Find the sniper pieces.
            const uint64_t snipers =
                    (attackBoard<Rook>(0, ksq) &
                    (board->getPieces<them, Rook>() | theirQueens)) |
                    (attackBoard<Bishop>(0, ksq) &
                    (board->getPieces<them, Bishop>() | theirQueens));

            // Iterate through the snipers and draw paths to the king,
            // using these paths as an x-ray to find the blockers.
            for (uint64_t s = snipers; s; s &= s - 1) {
                const int      ssq     = bitScanFwd(s);
                const uint64_t blocker = pathBoard(ssq, ksq) & allPieces;
                if(blocker && !(blocker & (blocker - 1))) blockers |= blocker;
            }

            // Determine which friendly pieces block sliding attacks on our
            // king.
            // If our king is in single check, determine the path between the
            // king and his attacker.
            const uint64_t kingGuard = ourPieces & blockers,
                            checkPath = (checkType == Check ? pathBoard(
                                    ksq, bitScanFwd(checkBoard)
                            ) | checkBoard : FullBoard),
            // A filter to limit all pieces to blocking
            // moves only in the event of single check
            // while simultaneously limiting generation
            // to "aggressive", "passive", or "all" move
            // types.
                            fullFilter = partialFilter & checkPath;
                            
            ///////////////////////////////////////////////////////////////
            switch(pt)
            {
                case Pawn:
                    return verifyPawnMove<us>(board, checkPath, kingGuard, ksq, move);
                case Rook:
                    return verifyMove<us,   Rook>(board, kingGuard, fullFilter, ksq, move);
                case Knight:
                    return verifyMove<us, Knight>(board, kingGuard, fullFilter, ksq, move);
                case Bishop:
                    return verifyMove<us, Bishop>(board, kingGuard, fullFilter, ksq, move);
                case Queen:
                    return verifyMove<us,  Queen>(board, kingGuard, fullFilter, ksq, move);
                default: 
                    assert(false);
            }
            //////////////////////////////////////////////////////////////
        }
    } // namespace (anon)

    namespace MoveVerifier {
        bool verify(Board *const board, Move move, PieceType pt) {
            return board->currentPlayer() == White ?
                   verifyMove<White>(board, move, pt):
                   verifyMove<Black>(board, move, pt);
        }
    }
} // namespace Homura