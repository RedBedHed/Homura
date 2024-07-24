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
         * A function to make promotions and under-promotions.
         *
         * @param moves a pointer to a list to populate
         *              with moves
         * @param o     the origin square
         * @param d     the destination square
         */
        inline Move*
        makePromotions(Move* moves, const int o, const int d) {
            // Order the promotions by value, gained 28 elo.
            *moves++ = Move::makePromotion<Queen >(o, d);
            *moves++ = Move::makePromotion<Rook  >(o, d);
            *moves++ = Move::makePromotion<Bishop>(o, d);
            *moves++ = Move::makePromotion<Knight>(o, d);
            return moves;
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
        template <Alliance A, FilterType FT>
        Move* makePawnMoves(Board* const board,
                            const uint64_t checkPath,
                            const uint64_t kingGuard,
                            const int kingSquare,
                            Move* moves) {
            static_assert(A == White || A == Black);
            static_assert(FT >= Aggressive && FT <= All);

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

            // If generating passive moves or all moves.
            if constexpr (FT != Aggressive) {
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

                // Make moves from passive one-square targets.
                for (int d; p1; p1 &= p1 - 1) {
                    d = bitScanFwd(p1);
                    *moves++ = Move::make((d + x->down), d);
                }

                // Make moves from passive two-square targets.
                for (int d; p2; p2 &= p2 - 1) {
                    d = bitScanFwd(p2);
                    *moves++ =
                        Move::make<PawnJump>((d + x->down + x->down), d);
                }
            }

            // If generating all moves or attack moves, continue,
            // otherwise return.
            if constexpr (FT != Passive) {
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

                // Make moves from aggressive right targets.
                for (int d; ar; ar &= ar - 1) {
                    d = bitScanFwd(ar);
                    *moves++ = Move::make(d + x->downLeft, d);
                }

                // Make moves from aggressive left targets.
                for (int d; al; al &= al - 1) {
                    d = bitScanFwd(al);
                    *moves++ = Move::make(d + x->downRight, d);
                }
            }

            // Generate single and double pushes for pinned low pawns,
            // if any.
            // Generate left and right attack moves for pinned low pawns,
            // if any.
            if (pinnedLowPawns) {
                if constexpr (FT != Aggressive) {
                    // All pseudo-legal, passive targets one square ahead.
                    uint64_t p1 = shift<x->up>(pinnedLowPawns) & emptySquares;

                    // All pseudo-legal, passive targets two squares ahead.
                    uint64_t p2 = shift<x->up>(p1 & x->pawnJumpSquares)
                                  & emptySquares;

                    // Intersect the pushes with the current checkPath.
                    p1 &= checkPath;
                    p2 &= checkPath;

                    // Make legal moves from passive one-square
                    // pseudo-legal targets.
                    // These moves must have a destination on
                    // the pinning ray.
                    for (int d, o; p1; p1 &= p1 - 1) {
                        d = bitScanFwd(p1);
                        o = d + x->down;
                        if (rayBoard(kingSquare, o) & p1 &
                            (uint64_t) -(int64_t) p1)
                            *moves++ = Move::make(o, d);
                    }

                    // Make legal moves from passive two-square
                    // pseudo-legal targets.
                    // These moves must have a destination on
                    // the pinning ray.
                    for (int d, o; p2; p2 &= p2 - 1) {
                        d = bitScanFwd(p2);
                        o = d + x->down + x->down;
                        if (rayBoard(kingSquare, o) & p2 &
                            (uint64_t) -(int64_t) p2)
                            *moves++ = Move::make<PawnJump>(o, d);
                    }
                }

                if constexpr (FT != Passive) {
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

                    // Make legal moves from pseudo-legal aggressive
                    // right targets. Only consider destinations that
                    // lie on the pinning ray.
                    for (int d, o; ar; ar &= ar - 1) {
                        d = bitScanFwd(ar);
                        o = d + x->downLeft;
                        if (rayBoard(kingSquare, o) & ar &
                           (uint64_t) -(int64_t) ar)
                            *moves++ = Move::make(o, d);
                    }

                    // Make legal moves from pseudo-legal aggressive
                    // left targets. Only consider destinations that
                    // lie on the pinning ray.
                    for (int d, o; al; al &= al - 1) {
                        d = bitScanFwd(al);
                        o = d + x->downRight;
                        if (rayBoard(kingSquare, o) & al &
                           (uint64_t) -(int64_t) al)
                            *moves++ = Move::make(o, d);
                    }
                }
            }

            // Generate promotion moves for free high pawns.
            if (freeHighPawns) {
                if constexpr (FT != Aggressive) {
                    // Calculate single promotion push.
                    // All legal promotion targets one square ahead.
                    uint64_t p1 = shift<x->up>(freeHighPawns) &
                                  emptySquares & checkPath;

                    // Make promotion moves from single push.
                    for(int d; p1; p1 &= p1 - 1){
                        d = bitScanFwd(p1);
                        moves = makePromotions(moves, d + x->down, d);
                    }
                }

                if constexpr (FT != Passive) {
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

                    // Make moves from aggressive right targets.
                    for (int d; ar; ar &= ar - 1) {
                        d = bitScanFwd(ar);
                        moves = makePromotions(moves, d + x->downLeft, d);
                    }

                    // Make moves from aggressive left targets.
                    for (int d; al; al &= al - 1) {
                        d = bitScanFwd(al);
                        moves = makePromotions(moves, d + x->downRight, d);
                    }
                }
            }

            // Generate promotion moves for pinned high pawns.
            if (pinnedHighPawns) {
                if constexpr (FT != Aggressive) {
                    // Calculate single promotion push for pinned pawns.
                    // All pseudo-legal promotion targets one square ahead.
                    uint64_t p1 =
                            shift<x->up>(pinnedHighPawns) & emptySquares & checkPath;

                    // Make legal promotion moves from pseudo-legal targets.
                    for (int o, d; p1; p1 &= p1 - 1){
                        d = bitScanFwd(p1);
                        o = d + x->down;
                        if (rayBoard(kingSquare, o) &
                            p1 & (uint64_t) - (int64_t)p1)
                            moves = makePromotions(moves, o, d);
                    }
                }

                if constexpr (FT != Passive) {
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

                    // Make legal promotion moves from aggressive right targets.
                    for (int o, d; ar; ar &= ar - 1) {
                        d = bitScanFwd(ar);
                        o = d + x->downLeft;
                        if (rayBoard(kingSquare, o) &
                            ar & (uint64_t) - (int64_t)ar)
                            moves = makePromotions(moves, o, d);
                    }

                    // Make legal promotion moves from aggressive left targets.
                    for (int o, d; al; al &= al - 1) {
                        d = bitScanFwd(al);
                        o = d + x->downRight;
                        if (rayBoard(kingSquare, o) &
                            al & (uint64_t) - (int64_t)al)
                            moves = makePromotions(moves, o, d);
                    }
                }
            }

            // If the filter type is not passive, continue.
            if constexpr (FT == Passive) return moves;

            // Find the en passant square, if any.
            const int enPassantSquare = board->getEpSquare();

            // If the en passant square is set, continue.
            if (enPassantSquare == NullSQ) return moves;

            // The en passant pawn square board.
            const uint64_t eppBoard  = SquareToBitBoard[enPassantSquare];

            // The en passant destination board.
            const uint64_t destBoard = shift<x->up>(eppBoard);

            // If we are in single check and the destination
            // doesn't block... and if the en passant pawn is
            // not the king's attacker... Don't generate an en
            // passant move.
            if (!(destBoard & checkPath) &&
                !(eppBoard  & SquareToPawnAttacks[us][kingSquare]))
                    return moves;

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
                return moves;

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
                            return moves;
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
                            return moves;
                    }
                }
            }

            // Calculate the destination square.
            const int destinationSquare = enPassantSquare + x->up;

            // Add free-pass en passant moves.
            for(uint64_t fp = freePasses; fp; fp &= fp - 1) {
                const int o = bitScanFwd(fp);
                *moves++ = Move::make<EnPassant>(o, destinationSquare);
            }

            // Add pinned-pass en passant moves.
            for(uint64_t pp = pinnedPasses; pp; pp &= pp - 1) {
                const int o = bitScanFwd(pp);
                if(destBoard & rayBoard(kingSquare, o))
                    *moves++ =
                        Move::make<EnPassant>(o, destinationSquare);
            }

            return moves;
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
        Move* makeMoves(Board* const board,
                               const uint64_t kingGuard,
                               const uint64_t filter,
                               const int kingSquare,
                               Move* moves) {
            static_assert(A == White || A == Black);
            static_assert(PT >= Rook && PT <= Queen);

            constexpr const Alliance us = A;

            // Initialize constants.
            const uint64_t pieceBoard = board->getPieces<us, PT>(),
                           freePieces = pieceBoard & ~kingGuard,
                           allPieces  = board->getAllPieces();

            // Calculate moves for free pieces.
            // Traverse the free piece bit board.
            for (uint64_t n = freePieces; n; n &= n - 1) {

                // Find an origin square.
                const int origin = bitScanFwd(n);

                // Look up the attack board using the origin
                // square and intersect with the filter.
                uint64_t ab = attackBoard<PT>(allPieces, origin)
                    & filter;

                // Traverse through the legal
                // move board and add all legal moves.
                for (; ab; ab &= ab - 1)
                    *moves++ = Move::make(origin, bitScanFwd(ab));
            }

            // Knight pinned pieces are trapped. They
            // cannot move along the pinning ray.
            if constexpr (PT == Knight) return moves;

            // All pieces pinned between the king and an
            // attacker.
            const uint64_t pinnedPieces = pieceBoard & kingGuard;

            // If there are pinned pieces, generate their legal
            // moves.
            if (pinnedPieces) {

                // Calculate moves for pinned pieces.
                // Traverse the pinned piece bitboard.
                uint64_t n = pinnedPieces;
                do {

                    // Find an origin square.
                    const int origin = bitScanFwd(n);

                    // Lookup the attack board and intersect with
                    // the filter and the pinning ray.
                    uint64_t ab =
                        attackBoard<PT>(allPieces, origin)
                            & filter & rayBoard(kingSquare, origin);

                    // Traverse through the legal
                    // move board and add all legal moves.
                    for (; ab; ab &= ab - 1)
                        *moves++ = Move::make(origin, bitScanFwd(ab));

                    n &= n - 1;
                } while (n);
            }

            return moves;
        }

        /**
         * A function to generate moves for every piece type.
         *
         * @tparam A    the alliance to consider
         * @tparam FT   the filter type
         * @param board the current game board
         * @param moves a pointer to the list to populate
         */
        template <Alliance A, FilterType FT>
        uint64_t makeMoves(Board* const board, Move* moves) {
            static_assert(A == White || A == Black);
            static_assert(FT >= Aggressive && FT <= All);

            const Move* const initialMove = moves;
            constexpr const Alliance us = A, them = ~us;

            // Initialize constants.
            const uint64_t allPieces     = board->getAllPieces(),
                           ourPieces     = board->getPieces<us>(),
                           theirPieces   = board->getPieces<them>(),
                           partialFilter = FT == All?     ~ourPieces :
                                           FT == Passive? ~allPieces :
                                                          theirPieces,
                           king          = board->getPieces<us, King>();

            // Get the board defaults for our alliance.
            constexpr const Defaults* const x = defaults<us>();

            // Find the king square.
            const int ksq = bitScanFwd(king);

            // Find all pieces that attack our king.
            const uint64_t checkBoard = attacksOn<us, King>(board, ksq);

            // Calculate the check type for our king.
            const CheckType checkType = calculateCheck(checkBoard);

            // If our king is in double check, then only king moves
            // should be considered.
            if (checkType != DoubleCheck) {
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

                // Make non-king moves.
                moves = makeMoves<us,  Queen>(board, kingGuard, fullFilter, ksq, moves);
                moves = makeMoves<us, Knight>(board, kingGuard, fullFilter, ksq, moves);
                moves = makeMoves<us, Bishop>(board, kingGuard, fullFilter, ksq, moves);
                moves = makeMoves<us,   Rook>(board, kingGuard, fullFilter, ksq, moves);
                moves = makePawnMoves<us, FT>(board, checkPath, kingGuard,  ksq, moves);
            }

            // Generate normal king moves.
            uint64_t d = SquareToKingAttacks[ksq];
            for (d &= partialFilter; d; d &= d - 1) {
                const int dest = bitScanFwd(d);
                if (!attacksOn<us, King>(board, dest))
                    *moves++ = Move::make(ksq, dest);
            }

            // If the filter type is aggressive, then castling moves
            // are irrelevant. If we don't have castling rights or
            // if we are in check, then castling moves are illegal.
            if (FT == Aggressive || checkType != None)
                return (moves - initialMove);

            // Generate king-side castle.
            if(!(x->kingSideMask & allPieces) &&
                board->hasCastlingRights<us, KingSide>() &&
                safeSquares<us>(board, x->kingSideCastlePath))
                *moves++ = Move::make<Castling>(
                        ksq, x->kingSideDestination
                );

            // Generate queen-side castle.
            if(!(x->queenSideMask & allPieces) &&
                board->hasCastlingRights<us, QueenSide>() &&
                safeSquares<us>(board, x->queenSideCastlePath))
                *moves++ = Move::make<Castling>(
                        ksq, x->queenSideDestination
                );

            return (moves - initialMove);
        }

        inline uint32_t getValue(Board* const board, Move move) {
            if(move.moveType() == Castling)
                return 0;
            else if(move.moveType() == EnPassant)
                return 100;

            uint32_t score = see_values[board->getPiece(move.destination())];

            if(move.isPromotion())
                score += see_values[move.promotionPiece()] - 100;

            return score;
        }

        constexpr PieceType getNextVictim(Board* const b, 
                                          Alliance a, 
                                          uint64_t attackers) {
            if(attackers & b->getPieces(a, Pawn))   return Pawn;
            if(attackers & b->getPieces(a, Knight)) return Knight;
            if(attackers & b->getPieces(a, Bishop)) return Bishop;
            if(attackers & b->getPieces(a, Rook))   return Rook;
            if(attackers & b->getPieces(a, Queen))  return Queen;
            if(attackers & b->getPieces(a, King))   return King;
            return NullPT;
        }

        template<Alliance A>
        bool see_(Board* const board, Move move, int thresh) {

            constexpr Alliance us = A, them = ~A;

            int32_t score = getValue(board, move) - thresh;

            if(score < 0) return false;

            score -= see_values[
                move.isPromotion()? 
                move.promotionPiece(): 
                board->getPiece(move.origin())
            ];

            if(score >= 0) return true;

            const uint32_t sq = move.destination();

            uint64_t occupied = 
                board->getAllPieces() ^ 
                SquareToBitBoard[move.origin()] ^ 
                SquareToBitBoard[move.destination()];

            if(move.moveType() == EnPassant)
                occupied ^= SquareToBitBoard[board->getEpSquare()];

            const uint64_t queens  = board->getPieces<us, Queen>() | 
                                     board->getPieces<them, Queen>();
            const uint64_t bishops = board->getPieces<us, Bishop>() | 
                                     board->getPieces<them, Bishop>() | queens;
            const uint64_t rooks   = board->getPieces<us, Rook>() | 
                                     board->getPieces<them, Rook>() | queens;

            uint64_t attackers = attacksOn(board, occupied, sq);

            Alliance a = them;

            for(;;)
            {
                uint64_t attackers_ = attackers & board->getPieces(a);
                if(attackers_ == 0)
                    break;

                PieceType pt = getNextVictim(board, a, attackers_);

                occupied ^= SquareToBitBoard[bitScanFwd(attackers_ & board->getPieces(a, pt))];

                if(pt == Pawn || pt == Bishop || pt == Queen)
                    attackers |= attackBoard<Bishop>(occupied, sq) & bishops;

                if(pt == Rook || pt == Queen)
                    attackers |= attackBoard<Rook>(occupied, sq) & rooks;

                attackers &= occupied;

                score = -score - 1 - see_values[pt];

                a = ~a;

                if(score >= 0)
                {
                    if(pt == King && (attackers & board->getPieces(a)))
                        a = ~a;
                    break;
                }
            }

            // Won't reach here.
            return a != us;
        }

        bool see(Board* const board, Move move, int thresh)
        {
            return board->currentPlayer() == White ?
                    see_<White>(board, move, thresh) :
                    see_<Black>(board, move, thresh) ;
        }
    } // namespace (anon)

    namespace MoveFactory {

        template<FilterType FT>
        inline int generateMoves(Board *const board, Move* const moves) {
            static_assert(FT >= Aggressive && FT <= All);
            return board->currentPlayer() == White ?
                   makeMoves<White, FT>(board, moves) :
                   makeMoves<Black, FT>(board, moves);
        }

        // Explicit instantiations.
        template int generateMoves<Aggressive>(Board*, Move*);
        template int generateMoves<Passive>(Board*, Move*);
        template int generateMoves<All>(Board*, Move*);

        control::control() { clearHistory(); }

        void control::clearHistory() {
            for(int i = 0; i < 2; ++i) 
                for(int j = 0; j < 64; ++j) 
                    for(int k = 0; k < 64; ++k) 
                        history[i][j][k] = 0;
            for(int i = 0; i < MaxDepth; ++i) 
                for(int j = 0; j < 2; ++j)
                    killers[i][j] = NullMove;
            for(int i = 0; i < MaxDepth; ++i)
                iidMoves[i] = NullMove;
            constexpr double m1 = 1.001204250630;
            constexpr double m2 = 1.502405984023;
            for(int i = 0; i < MaxDepth; ++i)
                for(int j = 0; j < 256; ++j)
                    reductions[i][j] = 
                        int32_t(
                            m1 * (double(i) /  4.0) + 
                            m2 * (double(j) / 12.0)
                        );
            for(int j = 0; j < 256; ++j)
                pv_reductions[j] = 
                    int32_t( 
                        m2 * (double(j) / 12.0)
                    );
        }

        void control::addKiller(int depth, Move m) {
            if(killers[depth][0] == m)
                return;
            killers[depth][1] = killers[depth][0];
            killers[depth][0] = m;
        }

        bool control::isKiller(int depth, Move m) 
        { return killers[depth][0] == m || killers[depth][1] == m; }

        void control::ageHistory() {

            // The history is good.
            // We like accurate history.
            // We shouldn't clear the
            // history completely at
            // the start of a search,
            // or when its values become 
            // too large. Instead, keep
            // half of each entry and 
            // continue to improve the 
            // accuracy of the history.
            // Idea from Blunder.
            for(int i = 0; i < 2; ++i) {
                for(int j = 0; j < 64; ++j) {
                    for(int k = 0; k < 64; ++k) {
                        history[i][j][k] >>= 1U;
                    }
                }
            }
        }

        template<Alliance A>
        void control::updateHistory(int origin, int dest, int depth) {
            history[A][origin][dest] += depth*depth;   
            if (history[A][origin][dest] >= INT32_MAX - 39)
                ageHistory();
        }

        template void control::updateHistory<White>(int, int, int);
        template void control::updateHistory<Black>(int, int, int);

        template<Alliance A>
        void control::decayHistory(int origin, int dest, int depth) {
            history[A][origin][dest] -= depth*depth;
            if (history[A][origin][dest] <= -INT32_MAX + 39)
                ageHistory();
        }

        template void control::decayHistory<White>(int, int, int);
        template void control::decayHistory<Black>(int, int, int);

        template<Alliance A>
        void control::raiseHistory(int origin, int dest, int depth) {
            history[A][origin][dest] += depth;   
            if (history[A][origin][dest] >= INT32_MAX - 39)
                ageHistory();
        }

        template void control::raiseHistory<White>(int, int, int);
        template void control::raiseHistory<Black>(int, int, int);

        template<>
        void control::removeHistory<Black>(int origin, int dest, int depth) 
        { history[Black][origin][dest] -= 1; }

        template<>
        void control::removeHistory<White>(int origin, int dest, int depth) 
        { history[White][origin][dest] -= 1; }

        template<>
        uint64_t control::getHistory<Black>(int origin, int dest) 
        { return history[Black][origin][dest]; }

        template<>
        uint64_t control::getHistory<White>(int origin, int dest) 
        { return history[White][origin][dest]; }

        /**
         * A dumpster fire, yes... But a (hopefully) fast dumpster fire.
         * 
         * @tparam ST the search type.
         * @param b a pointer to the board.
         * @param q a pointer to the search controls.
         * @param d the depth (ply in this case).
         */
        template<SearchType ST>
        MoveList<ST>::MoveList(Board* const b, control* const q, const int d) {
            static_assert(ST == AB || ST == Q);
            idx = -1;

            // Generate attacks.
            size = generateMoves<Aggressive>(b, m);
            int i = 0;
            for(; i < size; ++i) {            
                if(m[i] == q->pvMove)
                    p[i] = INT64_MAX;
                else if(m[i].isPromotion())
                    p[i] = INT32_MAX;
                else p[i] = ((see(b, m[i], 0))? INT32_MAX: INT32_MAX - 39) + val
                    [(uint32_t) b->getPiece(m[i].destination())]
                    [(uint32_t) b->getPiece(m[i].origin())     ];
            }

            if constexpr (ST == Q)
                return;

            qIdx = 0;
            mid = m + size;
            size += generateMoves<Passive>(b, mid); 
            for(; i < size; ++i) {
                if(m[i] == q->pvMove)
                    p[i] = INT64_MAX;
                else if(m[i].isPromotion())
                    p[i] = INT32_MAX;
                else if(m[i] == q->killers[d][0])
                    p[i] = INT32_MAX-1;
                else if(m[i] == q->killers[d][1])
                    p[i] = INT32_MAX-2;
                else
                    p[i] =
                        q->history
                        [b->currentPlayer()]
                        [m[i].origin()     ]
                        [m[i].destination()];
            }
        }

        template MoveList<AB>::MoveList(Board*, control*, int);
        template MoveList<Q>::MoveList(Board*, control*, int);

        template<> MoveList<MCTS>::MoveList(Board* const b) 
        { idx = 0; size = generateMoves<All>(b, m); }
    }
} // namespace Homura