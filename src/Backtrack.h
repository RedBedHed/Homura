//
// Created by evcmo on 8/12/2021.
//

#pragma once
#ifndef HOMURA_BACKTRACK_H
#define HOMURA_BACKTRACK_H

#include "MoveMake.h"
#include "Zobrist.h"
#include "Eval.h"

namespace Homura {

    // Using...
    using std::chrono::milliseconds;
    using std::chrono::time_point;
    using std::chrono::system_clock;
    using namespace MoveFactory;
    using namespace std::chrono;

    /**
     * Late Move Pruning margins by depth.
     */
    constexpr uint8_t lmpMargins[] = 
    { 0, 10, 15, 20, 25, 30 };

    enum : uint32_t {
        /**
         * The R value for null-move searches.
         */
        NULL_R = 2,

        /**
         * Reverse Futility (Static Null Move Pruning)
         * maximum remaining depth.
         */
        RFP_RD = 5,

        /**
         * Null Move Pruning minimum remaining depth.
         */
        NMP_RD = 2,

        /**
         * Razoring maximum remaining depth.
         */
        RAZ_RD = 2,

        /**
         * Internal Iterative Deepening minimum remaining
         * depth.
         */
        IID_RD = 4,

        /**
         * Internal Iterative Deepening R value.
         */
        IID_R  = 3, 

        /**
         * Late Move Pruning maximum remaining depth.
         */
        LMP_RD = 5,

        /**
         * Futility Pruning maximum remaining depth.
         */
        FUT_RD = 8,

        /**
         * Late Move Reductions minimum remaining depth.
         */
        LMR_RD = 2
    };


    /**
     * Basic node types enumerated.
     */
    enum NodeType : uint8_t { ROOT, IID, PV, NONPV };

    /**
     * A method to indicate whether the search should
     * abort.
     * 
     * @param time the time allotted
     * @param epoch the starting timestamp
     * @return whether the difference between the
     * current timestamp and the starting timestamp
     * is greater than or equal to the time allotted.
     */
    inline bool abort(int time, timer_t epoch) {
        auto clock = 
        (system_clock::now() - epoch);
        long long ms = duration_cast
        <milliseconds>(clock).count();
        return ms >= time;
    }

    /**
     * A method to measure the elapsed time of
     * the search.
     * 
     * @param epoch the starting timestamp
     * @return the difference between the current 
     * timestamp and the starting timestamp
     */
    inline long long elapsed(timer_t epoch) {
        auto clock = 
        (system_clock::now() - epoch);
        return duration_cast<milliseconds>
        (clock).count();
    }

    /**
     * A full, classical iterative deepening
     * search, for science.
     */
    // Move search(Board*, char*, control&, int);
    
    /**
     * A classical backtracking Alpha-Beta search.
     */
    template<Alliance A, NodeType NT, bool DO_NULL = true, bool CUT_NODE = false>
    int32_t alphaBeta
        (
        Board*, 
        int,
        int,
        int32_t, 
        int32_t,
        control*
        );

    /**
     * A classical backtracking quiescence search.
     */
    template<Alliance A, NodeType NT>
    int32_t quiescence
        (
        Board*, 
        int,
        int,
        int32_t, 
        int32_t,
        control*
        );

    Move search
        (
        Board *const b,
        char* info,
        control& q,
        int time
        );
}
#endif //HOMURA_BACKTRACK_H