(*
  Copyright © 2022 Barry Schwartz

  This program is free software: you can redistribute it and/or
  modify it under the terms of the GNU General Public License, as
  published by the Free Software Foundation, either version 3 of the
  License, or (at your option) any later version.

  This program is distributed in the hope that it will be useful, but
  WITHOUT ANY WARRANTY; without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
  General Public License for more details.

  You should have received copies of the GNU General Public License
  along with this program. If not, see
  <https://www.gnu.org/licenses/>.
*)

#define ATS_PACKNAME "ats2-patience-sort"
#define ATS_EXTERN_PREFIX "ats2_patience_sort_"

#define ATS_DYNLOADFLAG 0

#include "share/atspre_staload.hats"

staload "patience-sort/SATS/patience-sort.sats"

stadef index_t (ifirst : int, len : int, i : int) =
  patience_sort_index_t (ifirst, len, i)
typedef index_t (ifirst : int, len : int, i : int) =
  patience_sort_index_t (ifirst, len, i)
typedef index_t (ifirst : int, len : int) =
  patience_sort_index_t (ifirst, len)

stadef link_t (ifirst : int, len : int, i : int) =
  patience_sort_link_t (ifirst, len, i)
typedef link_t (ifirst : int, len : int, i : int) =
  patience_sort_link_t (ifirst, len, i)
typedef link_t (ifirst : int, len : int) =
  patience_sort_link_t (ifirst, len)

extern praxi
array_v_takeout_two
          {a     : vt@ype}
          {p     : addr}
          {n     : int}
          {i, j  : nat | i < n; j < n; i != j}
          (pfarr : array_v (a, p, n))
    :<prf> @(a @ (p + (i * sizeof a)),
             a @ (p + (j * sizeof a)),
             (a @ (p + (i * sizeof a)),
              a @ (p + (j * sizeof a))) -<lin,prf> array_v (a, p, n))

extern praxi
array_uninitize_without_doing_anything
          {a   : vt@ype}
          {n   : int}
          (arr : &array (INV(a), n) >> array (a?, n),
           asz : size_t n)
    :<prf> void

extern praxi
array_v_uninitize_without_doing_anything
          {a   : vt@ype}
          {p   : addr}
          {n   : int}
          (arr : !array_v (INV(a), p, n) >> array_v (a?, p, n))
    :<prf> void

extern fn {tk : tkind}
next_power_of_two
          {i : pos}
          (i : g1uint (tk, i))
    :<> [k : int | i <= k; k < 2 * i]
        [n : nat]
        @(EXP2 (n, k) | g1uint (tk, k))

(* ================================================================ *)
(*

  In the following implementation of next_power_of_two:

    * I implement it as a template for all types of kind g1uint. This
      includes dependent forms of uint, usint, ulint, ullint, size_t,
      and yet more types in the prelude; also whatever others one may
      create.

    * I prove the result is not less than the input.

    * I prove the result is less than twice the input.

    * I prove the result is a power of two. This last proof is
      provided in the form of an EXP2 prop.

    * I do NOT return what number two is raised to (though I easily
      could have). I leave that number "existentially defined". In
      other words, I prove only that some such non-negative number
      exists.

*)

implement {tk}
next_power_of_two {i} (i) =
  let
    (* This is not the fastest implementation, although it does verify
       its own correctness. *)

    val one : g1uint (tk, 1) = g1u2u 1u

    fun
    loop {j  : pos | j < i} .<i + i - j>.
         (pf : [n : nat] EXP2 (n, j) |
          j  : g1uint (tk, j))
        :<> [k : int | i <= k; k < 2 * i]
            [n : nat]
            @(EXP2 (n, k) | g1uint (tk, k)) =
      let
        val j2 = j + j
      in
        if i <= j2 then
          @(EXP2ind pf | j2)
        else
          loop (EXP2ind pf | j2)
      end
  in
    if i = one then
      @(EXP2bas () | one)
    else
      loop (EXP2bas () | one)
  end

(* ================================================================ *)
(* The patience sort.                                               *)

fn {a : vt@ype}
find_pile {ifirst, len : int}
          {n           : int | ifirst + len <= n}
          {num_piles   : nat | num_piles <= len}
          {n_piles     : int | len <= n_piles}
          {q           : pos | q <= len}
          (ifirst      : size_t ifirst,
           arr         : &RD(array (a, n)),
           num_piles   : size_t num_piles,
           piles       : &RD(array (link_t (ifirst, len), n_piles)),
           q           : size_t q)
    :<> [i : pos | i <= num_piles + 1]
        size_t i =
  (*
    Bottenbruch search for the leftmost pile whose top is greater than
    or equal to the next value dealt by "deal".

    References:

      * H. Bottenbruch, "Structure and use of ALGOL 60", Journal of
        the ACM, Volume 9, Issue 2, April 1962, pp.161-221.
        https://doi.org/10.1145/321119.321120

        The general algorithm is described on pages 214 and 215.

      * https://en.wikipedia.org/w/index.php?title=Binary_search_algorithm&oldid=1062988272#Alternative_procedure
  *)
  if num_piles = i2sz 0 then
    i2sz 1
  else
    let
      macdef lt = patience_sort$lt<a>

      prval () = lemma_g1uint_param ifirst
      prval () = prop_verify {0 <= ifirst} ()

      fun
      loop {j, k  : nat | j <= k; k < num_piles}
           .<k - j>.
           (arr   : &RD(array (a, n)),
            piles : &array (link_t (ifirst, len), n_piles),
            j     : size_t j,
            k     : size_t k)
          :<> [i : pos | i <= num_piles + 1]
              size_t i =
        if j = k then
          begin
            if succ j <> num_piles then
              succ j
            else
              let
                val [piles_j : int] piles_j = piles[j]
                val () = $effmask_exn assertloc (piles_j <> g1u2u 0u)

                stadef i1 = (q - 1) + ifirst
                stadef i2 = (piles_j - 1) + ifirst
                val i1 = pred q + ifirst
                and i2 = pred piles_j + ifirst

                val () = $effmask_exn assertloc (i1 <> i2)

                prval @(pfelem1, pfelem2, fpf) =
                  array_v_takeout_two
                    {a} {..} {n} {i1, i2} (view@ arr)

                val x2_lt_x1 =
                  (!(ptr_add<a> (addr@ arr, i2)))
                    \lt (!(ptr_add<a> (addr@ arr, i1)))

                prval () = view@ arr := fpf (pfelem1, pfelem2)
              in
                if x2_lt_x1 then
                  succ (succ j)
                else
                  succ j
              end
          end
        else
          let
            typedef index (i : int) = [0 <= i; i < n] size_t i
            typedef index = [i : int] index i

            stadef i = j + ((k - j) / 2)
            val i : size_t i = j + half (k - j)

            val [piles_j : int] piles_j = piles[j]
            val () = $effmask_exn assertloc (piles_j <> g1u2u 0u)

            stadef i1 = (q - 1) + ifirst
            stadef i2 = (piles_j - 1) + ifirst
            val i1 = pred q + ifirst
            and i2 = pred piles_j + ifirst

            val () = $effmask_exn assertloc (i1 <> i2)

            prval @(pfelem1, pfelem2, fpf) =
              array_v_takeout_two {a} {..} {n} {i1, i2} (view@ arr)

            val x2_lt_x1 =
              (!(ptr_add<a> (addr@ arr, i2)))
                \lt (!(ptr_add<a> (addr@ arr, i1)))

            prval () = view@ arr := fpf (pfelem1, pfelem2)
          in
            if x2_lt_x1 then
              loop (arr, piles, i + 1, k)
            else
              loop (arr, piles, j, i)
          end
    in
      loop (arr, piles, g1u2u 0u, pred num_piles)
    end

fn {a : vt@ype}
deal_refparams
          {ifirst, len : int}
          {n           : int | ifirst + len <= n}
          (ifirst      : size_t ifirst,
           len         : size_t len,
           arr         : &RD(array (a, n)),
           piles       : &array (link_t (ifirst, len)?, len)
                           >> array (link_t (ifirst, len), len),
           links       : &array (link_t (ifirst, len)?, len)
                           >> array (link_t (ifirst, len), len))
    :<!wrt> [num_piles   : int | num_piles <= len]
            size_t num_piles =
  (*
    Dealing is done backwards through the arr array, so an array
    already sorted in the desired order will result in a single pile.
  *)
  let
    prval () = lemma_g1uint_param ifirst
    prval () = lemma_g1uint_param len

    typedef link_t (i : int) = link_t (ifirst, len, i)
    typedef link_t = link_t (ifirst, len)

    val zero : size_t 0 = g1u2u 0u
    val one : size_t 1 = g1u2u 1u
    val link_nil : link_t 0 = g1u2u 0u

    fun
    loop {q         : nat | q <= len}
         {m         : nat | m <= len}
         .<q>.
         (arr       : &RD(array (a, n)),
          q         : size_t q,
          piles     : &array (link_t, len) >> _,
          links     : &array (link_t, len) >> _,
          m         : size_t m)
        :<!wrt> [num_piles : nat | num_piles <= len]
                size_t num_piles =
      if q = i2sz 0 then
        m
      else
        let
          val i = find_pile {ifirst, len} (ifirst, arr, m, piles, q)

          (* We have no proof the number of elements will not exceed
             storage. However, we know it will not, because the number
             of piles cannot exceed the size of the input. Let us get
             a "proof" by runtime check. *)
          val () = $effmask_exn assertloc (i <= len)
        in
          links[pred q] := piles[pred i];
          piles[pred i] := q;
          if i = succ m then
            loop {q - 1} (arr, pred q, piles, links, succ m)
          else
            loop {q - 1} (arr, pred q, piles, links, m)
        end
  in
    array_initize_elt<link_t> (piles, len, link_nil);
    array_initize_elt<link_t> (links, len, link_nil);
    loop (arr, len, piles, links, zero)
  end

fn {a : vt@ype}
deal_valparams
          {ifirst, len : int}
          {n           : int | ifirst + len <= n}
          {p_piles     : addr}
          {p_links     : addr}
          (pf_piles    : !array_v (link_t (ifirst, len)?,
                                   p_piles, len)
                            >> array_v (link_t (ifirst, len),
                                        p_piles, len),
           pf_links    : !array_v (link_t (ifirst, len)?,
                                   p_links, len)
                            >> array_v (link_t (ifirst, len),
                                        p_links, len) |
           ifirst      : size_t ifirst,
           len         : size_t len,
           arr         : &RD(array (a, n)),
           p_piles     : ptr p_piles,
           p_links     : ptr p_links)
         :<!wrt> [num_piles   : int | num_piles <= len]
                 size_t num_piles =
  deal_refparams<a> {ifirst, len} {n}
                    (ifirst, len, arr, !p_piles, !p_links)

overload deal with deal_valparams
overload deal with deal_refparams

fn {a : vt@ype}
k_way_merge_refparams
          {ifirst, len : int}
          {n           : int | ifirst + len <= n}
          {num_piles   : pos | num_piles <= len}
          {power       : int | len <= power}
          (pf_exp2     : [exponent : nat] EXP2 (exponent, power) |
           arr         : &RD(array (a, n)),
           ifirst      : size_t ifirst,
           len         : size_t len,
           num_piles   : size_t num_piles,
           power       : size_t power,
           piles       : &array (link_t (ifirst, len), len) >> _,
           links       : &RD(array (link_t (ifirst, len), len)),
           winvals     : &array (link_t (ifirst, len)?, 2 * power)
                            >> _,
           winlinks    : &array (link_t (ifirst, len)?, 2 * power)
                            >> _,
           sorted      : &array (index_t (ifirst, len)?, len)
                            >> array (index_t (ifirst, len), len))
    :<!wrt> void =
  (*
    k-way merge by tournament tree.

    See Knuth, volume 3, and also
    https://en.wikipedia.org/w/index.php?title=K-way_merge_algorithm&oldid=1047851465#Tournament_Tree

    However, I store a winners tree instead of the recommended losers
    tree. If the tree were stored as linked nodes, it would probably
    be more efficient to store a losers tree. However, I am storing
    the tree as an array, and one can find an opponent quickly by
    simply toggling the least significant bit of a competitor's array
    index.
  *)
  let
    prval () = lemma_g1uint_param ifirst
    prval () = lemma_g1uint_param len

    typedef link_t (i : int) = link_t (ifirst, len, i)
    typedef link_t = link_t (ifirst, len)

    val link_nil : link_t 0 = g1u2u 0u

    typedef index_t (i : int) = index_t (ifirst, len, i)
    typedef index_t = index_t (ifirst, len)

    val [total_external_nodes : int]
        @(_ | total_external_nodes) = next_power_of_two num_piles
    prval () = prop_verify {num_piles <= total_external_nodes} ()

    stadef total_nodes = (2 * total_external_nodes) - 1
    val total_nodes : size_t total_nodes =
      pred (g1u2u 2u * total_external_nodes)

    (* We will ignore index 0 of the winners tree arrays. *)
    stadef winners_size = total_nodes + 1
    val winners_size : size_t winners_size = succ total_nodes

    (* An exercise for the reader is to write a proof that
       winners_size <= 2 * power, so one can get rid of the
       runtime assertion here: *)
    val () = $effmask_exn assertloc (winners_size <= 2 * power)

    prval @(winvals_left, winvals_right) =
      array_v_split {link_t?} {..} {2 * power} {winners_size}
                    (view@ winvals)
    prval () = view@ winvals := winvals_left

    prval @(winlinks_left, winlinks_right) =
      array_v_split {link_t?} {..} {2 * power} {winners_size}
                    (view@ winlinks)
    prval () = view@ winlinks := winlinks_left

    val () = array_initize_elt<link_t> (winvals, winners_size,
                                        link_nil)
    val () = array_initize_elt<link_t> (winlinks, winners_size,
                                        link_nil)


    (* - - - - - - - - - - - - - - - - - - - - - - - - - - *)
    (* Record which pile a winner will have come from.     *)

    fun
    init_pile_links
              {i : nat | i <= num_piles}
              .<num_piles - i>.
              (winlinks : &array (link_t, winners_size),
               i        : size_t i)
        :<!wrt> void =
      if i <> num_piles then
        begin
          winlinks[total_external_nodes + i] := succ i;
          init_pile_links (winlinks, succ i)
        end

    val () = init_pile_links (winlinks, g1u2u 0u)

    (* - - - - - - - - - - - - - - - - - - - - - - - - - - *)
    (* The top of each pile becomes a starting competitor. *)

    fun
    init_competitors
              {i : nat | i <= num_piles}
              .<num_piles - i>.
              (winvals : &array (link_t, winners_size),
               piles   : &array (link_t, len),
               i       : size_t i)
        :<!wrt> void =
      if i <> num_piles then
        begin
          winvals[total_external_nodes + i] := piles[i];
          init_competitors (winvals, piles, succ i)
        end
 
    val () = init_competitors (winvals, piles, g1u2u 0u)

    (* - - - - - - - - - - - - - - - - - - - - - - - - - - *)
    (* Discard the top of each pile.                       *)

    fun
    discard_tops {i : nat | i <= num_piles}
                 .<num_piles - i>.
                 (piles : &array (link_t, len),
                  links : &array (link_t, len),
                  i     : size_t i)
        :<!wrt> void =
      if i <> num_piles then
        let
          val link = piles[i]

          (* None of the piles should have been empty. *)
          val () = $effmask_exn assertloc (link <> g1u2u 0u)
        in
          piles[i] := links[pred link];
          discard_tops (piles, links, succ i)
        end

    val () = discard_tops (piles, links, g1u2u 0u)

    (* - - - - - - - - - - - - - - - - - - - - - - - - - - *)
    (* How to play a game.                                 *)
    
    fn
    play_game {i       : int | 2 <= i; i <= total_nodes}
              (arr     : &RD(array (a, n)),
               winvals : &array (link_t, winners_size),
               i       : size_t i)
        :<> [iwinner : pos | iwinner <= total_nodes]
            size_t iwinner =
      let
        macdef lt = patience_sort$lt<a>

        fn
        find_opponent {i : int | 2 <= i; i <= total_nodes}
                      (i : size_t i)
            :<> [j : int | 2 <= j; j <= total_nodes]
                size_t j =
          let
            (* The prelude contains bitwise operations only for
               non-dependent unsigned integer. We will not bother to
               add them ourselves, but instead go back and forth
               between dependent and non-dependent. *)
            val i0 = g0ofg1 i
            val j0 = g0uint_lxor<size_kind> (i0, g0u2u 1u)
            val j = g1ofg0 j0

            (* We have no proof the opponent is in the proper
               range. Create a "proof" by runtime checks. *)
            val () = $effmask_exn assertloc (g1u2u 2u <= j)
            val () = $effmask_exn assertloc (j <= total_nodes)
          in
            j
          end

        val j = find_opponent i
        val [winner_i : int] winner_i = winvals[i]
        and [winner_j : int] winner_j = winvals[j]
      in
        if winner_i = link_nil then
          j
        else if winner_j = link_nil then
          i
        else
          let
            stadef i1 = (winner_i - 1) + ifirst
            stadef i2 = (winner_j - 1) + ifirst
            val i1 = pred winner_i + ifirst
            and i2 = pred winner_j + ifirst
            prval () = lemma_g1uint_param i1
            prval () = lemma_g1uint_param i2

            val () = $effmask_exn assertloc (i1 <> i2)

            prval @(pfelem1, pfelem2, fpf) =
              array_v_takeout_two {a} {..} {n} {i1, i2} (view@ arr)

            val x2_lt_x1 =
              (!(ptr_add<a> (addr@ arr, i2)))
                \lt (!(ptr_add<a> (addr@ arr, i1)))

            prval () = view@ arr := fpf (pfelem1, pfelem2)
          in
            if x2_lt_x1 then j else i
          end
      end

    (* - - - - - - - - - - - - - - - - - - - - - - - - - - *)

    fun
    build_tree {istart : pos | istart <= total_external_nodes}
               .<istart>.
               (arr      : &RD(array (a, n)),
                winvals  : &array (link_t, winners_size),
                winlinks : &array (link_t, winners_size),
                istart   : size_t istart)
        :<!wrt> void =
      if istart <> 1 then
        let
          fun
          play_initial_games
                    {i : int | istart <= i; i <= (2 * istart) + 1}
                    .<(2 * istart) + 1 - i>.
                    (arr      : &RD(array (a, n)),
                     winvals  : &array (link_t, winners_size),
                     winlinks : &array (link_t, winners_size),
                     i        : size_t i)
              :<!wrt> void =
            if i <= pred (istart + istart) then
              let
                val iwinner = play_game (arr, winvals, i)
                and i2 = half i
              in
                winvals[i2] := winvals[iwinner];
                winlinks[i2] := winlinks[iwinner];
                play_initial_games (arr, winvals, winlinks,
                                    succ (succ i))
              end
        in
          play_initial_games (arr, winvals, winlinks, istart);
          build_tree (arr, winvals, winlinks, istart / g1u2u 2u)
        end

    val () = build_tree (arr, winvals, winlinks, total_external_nodes)

    (* - - - - - - - - - - - - - - - - - - - - - - - - - - *)

    fun
    replay_games {i : pos | i <= total_nodes}
                 .<i>.
                 (arr      : &RD(array (a, n)),
                  winvals  : &array (link_t, winners_size),
                  winlinks : &array (link_t, winners_size),
                  i        : size_t i)
        :<!wrt> void =
      if i <> g1u2u 1u then
        let
          val iwinner = play_game (arr, winvals, i)
          and i2 = i / g1u2u 2u
        in
          winvals[i2] := winvals[iwinner];
          winlinks[i2] := winlinks[iwinner];
          replay_games (arr, winvals, winlinks, i2)
        end

    fun
    merge {isorted  : nat | isorted <= len}
          {p_sorted : addr}
          .<len - isorted>.
          (pf_sorted : !array_v (index_t?, p_sorted,
                                 len - isorted)
                          >> array_v (index_t, p_sorted,
                                      len - isorted) |
           arr       : &RD(array (a, n)),
           piles     : &array (link_t, len),
           links     : &array (link_t, len),
           winvals   : &array (link_t, winners_size),
           winlinks  : &array (link_t, winners_size),
           p_sorted  : ptr p_sorted,
           isorted   : size_t isorted)
        :<!wrt> void =
      (* This function not only fills in the "sorted" array, but
         transforms it from "uninitialized" to "initialized". *)
      if isorted <> len then
        let
          prval @(pf_elem, pf_rest) = array_v_uncons pf_sorted
          val winner = winvals[1]
          val () = $effmask_exn assertloc (winner <> link_nil)
          val () = !p_sorted := pred winner + ifirst

          (* Move to the next element in the winner's pile. *)
          val ilink = winlinks[1]
          val () = $effmask_exn assertloc (ilink <> link_nil)
          val inext = piles[pred ilink]
          val () = (if inext <> link_nil then
                      piles[pred ilink] := links[pred inext])

          (* Replay games, with the new element as a competitor. *)
          val i = (total_nodes / g1u2u 2u) + ilink
          val () = $effmask_exn assertloc (i <= total_nodes)
          val () = winvals[i] := inext
          val () = replay_games (arr, winvals, winlinks, i)

          val () = merge (pf_rest |
                          arr, piles, links, winvals, winlinks,
                          ptr_succ<index_t> p_sorted, succ isorted)
          prval () = pf_sorted := array_v_cons (pf_elem, pf_rest)
        in
        end
      else
        let
          prval () = pf_sorted :=
            array_v_unnil_nil{index_t?, index_t} pf_sorted
        in
        end

    val () = merge (view@ sorted |
                    arr, piles, links, winvals, winlinks,
                    addr@ sorted, i2sz 0)

    prval () =
      array_uninitize_without_doing_anything
        (winvals, winners_size)
    prval () =
      array_uninitize_without_doing_anything
        (winlinks, winners_size)
    prval () = view@ winvals :=
      array_v_unsplit (view@ winvals, winvals_right)
    prval () = view@ winlinks :=
      array_v_unsplit (view@ winlinks, winlinks_right)
  in
  end

fn {a : vt@ype}
k_way_merge_valparams
          {ifirst, len : int}
          {n           : int | ifirst + len <= n}
          {num_piles   : pos | num_piles <= len}
          {power       : int | len <= power}
          {p_piles     : addr}
          {p_links     : addr}
          {p_winvals   : addr}
          {p_winlinks  : addr}
          (pf_exp2     : [exponent : nat] EXP2 (exponent, power),
           pf_piles    : !array_v (link_t (ifirst, len),
                                   p_piles, len) >> _,
           pf_links    : !array_v (link_t (ifirst, len),
                                   p_links, len) >> _,
           pf_winvals  : !array_v (link_t (ifirst, len)?,
                                   p_winvals, 2 * power) >> _,
           pf_winlinks : !array_v (link_t (ifirst, len)?,
                                   p_winlinks, 2 * power) >> _ |
           arr         : &RD(array (a, n)),
           ifirst      : size_t ifirst,
           len         : size_t len,
           num_piles   : size_t num_piles,
           power       : size_t power,
           p_piles     : ptr p_piles,
           p_links     : ptr p_links,
           p_winvals   : ptr p_winvals,
           p_winlinks  : ptr p_winlinks,
           sorted      : &array (index_t (ifirst, len)?, len)
                            >> array (index_t (ifirst, len), len))
    :<!wrt> void =
  k_way_merge_refparams<a>
    {ifirst, len} {n} {num_piles} {power}
    (pf_exp2 |
     arr, ifirst, len, num_piles, power,
     !p_piles, !p_links, !p_winvals, !p_winlinks, sorted)

overload k_way_merge with k_way_merge_refparams
overload k_way_merge with k_way_merge_valparams

implement {a}
patience_sort_given_workspace
          {ifirst, len} {n} {power} {n_workspace}
          (pf_exp2 | arr, ifirst, len, power, workspace, sorted) =
  let
    prval () = lemma_g1uint_param ifirst
    prval () = lemma_g1uint_param len

    typedef index_t = index_t (ifirst, len)
    typedef link_t = link_t (ifirst, len)
  in
    if len = i2sz 0 then
      let
        prval () = view@ sorted :=
          array_v_unnil_nil{index_t?, index_t} (view@ sorted)
      in
      end
    else
      let
        val p_piles = addr@ workspace
        and p_links = ptr_add<link_t> (addr@ workspace, len)

        prval @(pf_piles_and_links, pf_rest) =
          array_v_split {link_t?} {..} {n_workspace} {2 * len}
                        (view@ workspace)
        prval @(pf_piles, pf_links) =
          array_v_split {link_t?} {..} {2 * len} {len}
                        pf_piles_and_links

        val num_piles =
         deal {ifirst, len} {n}
              (pf_piles, pf_links |
               ifirst, len, arr, p_piles, p_links)
        prval () = lemma_g1uint_param num_piles
        val () = $effmask_exn assertloc (num_piles <> i2sz 0)

        (* FIXME: It may be advantageous to combine winvals and
                  winlinks in the manner of my original Fortran
                  program, where I used a 2-dimensional array with
                  values and links side-by-side. *)

        val p_winvals = ptr_add<link_t> (p_piles, 2 * len)
        and p_winlinks = ptr_add<link_t> (p_piles,
                                          (2 * len) + (2 * power))

        prval @(pf_winvals_and_winlinks, pf_rest) =
          array_v_split {link_t?} {..}
                        {n_workspace - (2 * len)} {4 * power}
                        pf_rest
        prval @(pf_winvals, pf_winlinks) =
          array_v_split {link_t?} {..} {4 * power} {2 * power}
                        pf_winvals_and_winlinks

        val () =
          k_way_merge {ifirst, len} {n} {..} {power}
                      (pf_exp2, pf_piles, pf_links,
                       pf_winvals, pf_winlinks |
                       arr, ifirst, len, num_piles, power,
                       p_piles, p_links, p_winvals, p_winlinks,
                       sorted)

        prval pf_winvals_and_winlinks =
          array_v_unsplit (pf_winvals, pf_winlinks)
        prval pf_rest =
          array_v_unsplit (pf_winvals_and_winlinks, pf_rest)

        prval () = array_v_uninitize_without_doing_anything pf_piles
        prval () = array_v_uninitize_without_doing_anything pf_links

        prval pf_piles_and_links =
          array_v_unsplit (pf_piles, pf_links)
        prval () = view@ workspace :=
          array_v_unsplit (pf_piles_and_links, pf_rest)
      in
      end
  end

(* ================================================================ *)
(* An interface that provides the workspace. If the subarray to     *)
(* be sorted is small enough, stack storage will be used.           *)

#define LEN_THRESHOLD  128
#define WINNERS_SIZE   256
#define WORKSPACE_SIZE 768

prval () = prop_verify {WINNERS_SIZE == 2 * LEN_THRESHOLD} ()
prval () = prop_verify {WORKSPACE_SIZE ==
                          (2 * LEN_THRESHOLD) + (2 * WINNERS_SIZE)} ()

local
  prval pf_exp2 = EXP2bas ()      (*   1*)
  prval pf_exp2 = EXP2ind pf_exp2 (*   2 *)
  prval pf_exp2 = EXP2ind pf_exp2 (*   4 *)
  prval pf_exp2 = EXP2ind pf_exp2 (*   8 *)
  prval pf_exp2 = EXP2ind pf_exp2 (*  16 *)
  prval pf_exp2 = EXP2ind pf_exp2 (*  32 *)
  prval pf_exp2 = EXP2ind pf_exp2 (*  64 *)
  prval pf_exp2 = EXP2ind pf_exp2 (* 128 *)
in
  prval pf_exp2_for_stack_storage = pf_exp2
end

implement {a}
patience_sort_with_its_own_workspace
          {ifirst, len} {n} (arr, ifirst, len, sorted) =
  let
    prval () = lemma_g1uint_param ifirst
    prval () = lemma_g1uint_param len

    typedef link_t = link_t (ifirst, len)

    fn
    sort {ifirst, len : int | 0 <= ifirst}
         {n           : int | ifirst + len <= n}
         {power       : int | len <= power}
         {n_workspace : int | (2 * len) + (4 * power) <= n_workspace}
         (pf_exp2     : [exponent : nat] EXP2 (exponent, power) |
          arr         : &RD(array (a, n)),
          ifirst      : size_t ifirst,
          len         : size_t len,
          power       : size_t power,
          workspace   : &array (link_t (ifirst, len)?, n_workspace)
                          >> _,
          sorted      : &array (index_t (ifirst, len)?, len)
                          >> array (index_t (ifirst, len), len))
        :<!wrt> void =
      patience_sort_given_workspace<a>
        {ifirst, len} {n} {power}
        (pf_exp2 | arr, ifirst, len, power, workspace, sorted)
  in
    if len <= i2sz LEN_THRESHOLD then
      let
        var workspace : array (link_t?, WORKSPACE_SIZE)
      in
        sort (pf_exp2_for_stack_storage |
              arr, ifirst, len, i2sz LEN_THRESHOLD, workspace, sorted)
      end
    else
      let
        val @(pf_exp2 | power) = next_power_of_two<size_kind> len
        val @(pf_workspace, pfgc_workspace | p_workspace) =
          array_ptr_alloc<link_t> ((2 * len) + (4 * power))
      in
        sort (pf_exp2 |
              arr, ifirst, len, power, !p_workspace, sorted);
        array_ptr_free (pf_workspace, pfgc_workspace | p_workspace)
      end
  end

(*------------------------------------------------------------------*)
