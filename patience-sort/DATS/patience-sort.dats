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
staload UN = "prelude/SATS/unsafe.sats"

staload "patience-sort/SATS/patience-sort.sats"

(* ================================================================ *)

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
              a @ (p + (j * sizeof a))) -<lin,prf>
  array_v (a, p, n))

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

stadef index_t (n : int, i : int) =
  patience_sort_index_t (n, i)
typedef index_t (tk : tkind, n : int, i : int) =
  patience_sort_index_t (tk, n, i)
typedef index_t (tk : tkind, n : int) =
  patience_sort_index_t (tk, n)

stadef link_t (n : int, i : int) =
  patience_sort_link_t (n, i)
typedef link_t (tk : tkind, n : int, i : int) =
  patience_sort_link_t (tk, n, i)
typedef link_t (tk : tkind, n : int) =
  patience_sort_link_t (tk, n)

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

fn {a  : vt@ype}
   {tk : tkind}
find_pile {n         : int}
          {num_piles : nat | num_piles <= n}
          {n_piles   : int | n <= n_piles}
          {q         : pos | q <= n}
          (arr       : &RD(array (a, n)),
           num_piles : g1uint (tk, num_piles),
           piles     : &RD(array (link_t (tk, n), n_piles)),
           q         : g1uint (tk, q))
    :<> [i : pos | i <= num_piles + 1]
        g1uint (tk, i) =
  (*
    Bottenbruch search for the *leftmost* pile whose *first* element
    is *greater* than or equal to the next value dealt by "deal".

    References:

      * H. Bottenbruch, "Structure and use of ALGOL 60", Journal of
        the ACM, Volume 9, Issue 2, April 1962, pp.161-221.
        https://doi.org/10.1145/321119.321120

        The general algorithm is described on pages 214 and 215.

      * https://en.wikipedia.org/w/index.php?title=Binary_search_algorithm&oldid=1062988272#Alternative_procedure
  *)
  if num_piles = g1u2u 0u then
    g1u2u 1u
  else
    let
      macdef lt = patience_sort$lt<a>

      fun
      loop {j, k  : nat | j <= k; k < num_piles}
           .<k - j>.
           (arr   : &RD(array (a, n)),
            piles : &array (link_t (tk, n), n_piles),
            j     : g1uint (tk, j),
            k     : g1uint (tk, k))
          :<> [i : pos | i <= num_piles + 1]
              g1uint (tk, i) =
        if j = k then
          begin
            if succ j <> num_piles then
              succ j
            else
              let
                val [piles_j : int] piles_j = piles[j]
                val () = $effmask_exn assertloc (piles_j <> g1u2u 0u)

                stadef i1 = q - 1
                stadef i2 = piles_j - 1
                val i1 = pred q
                and i2 = pred piles_j

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
                  succ num_piles
                else
                  num_piles
              end
          end
        else
          let
            typedef index (i : int) = [0 <= i; i < n] g1uint (tk, i)
            typedef index = [i : int] index i

            stadef i = j + ((k - j) / 2)
            val i : g1uint (tk, i) = j + half (k - j)

            val [piles_j : int] piles_j = piles[j]
            val () = $effmask_exn assertloc (piles_j <> g1u2u 0u)

            stadef i1 = q - 1
            stadef i2 = piles_j - 1
            val i1 = pred q
            and i2 = pred piles_j

            val () = $effmask_exn assertloc (i1 <> i2)

            prval @(pfelem1, pfelem2, fpf) =
              array_v_takeout_two {a} {..} {n} {i1, i2} (view@ arr)

            val x2_lt_x1 =
              (!(ptr_add<a> (addr@ arr, i2)))
                \lt (!(ptr_add<a> (addr@ arr, i1)))

            prval () = view@ arr := fpf (pfelem1, pfelem2)
          in
            if x2_lt_x1 then
              loop (arr, piles, succ i, k)
            else
              loop (arr, piles, j, i)
          end
    in
      loop (arr, piles, g1u2u 0u, pred num_piles)
    end

fn {a  : vt@ype}
   {tk : tkind}
find_last_elem
          {n            : int}
          {num_piles    : nat | num_piles <= n}
          {n_last_elems : int | n <= n_last_elems}
          {q            : pos | q <= n}
          (arr          : &RD(array (a, n)),
           num_piles    : g1uint (tk, num_piles),
           last_elems   : &RD(array (link_t (tk, n), n_last_elems)),
           q            : g1uint (tk, q))
    :<> [i : pos | i <= num_piles + 1]
        g1uint (tk, i) =
  (*
    Bottenbruch search for the *rightmost* pile whose *last* element
    is *less* than or equal to the next value dealt by "deal".

    References:

      * H. Bottenbruch, "Structure and use of ALGOL 60", Journal of
        the ACM, Volume 9, Issue 2, April 1962, pp.161-221.
        https://doi.org/10.1145/321119.321120

        The general algorithm is described on pages 214 and 215.

      * https://en.wikipedia.org/w/index.php?title=Binary_search_algorithm&oldid=1062988272#Alternative_procedure
  *)
  if num_piles = g1u2u 0u then
    g1u2u 1u
  else
    let
      macdef lt = patience_sort$lt<a>

      fun
      loop {j, k       : nat | j <= k; k < num_piles}
           .<k - j>.
           (arr        : &RD(array (a, n)),
            last_elems : &array (link_t (tk, n), n_last_elems),
            j          : g1uint (tk, j),
            k          : g1uint (tk, k))
          :<> [i : pos | i <= num_piles + 1]
              g1uint (tk, i) =
        if j = k then
          begin
            if succ j <> num_piles then
              num_piles - j
            else
              let
                stadef j0 = num_piles - 1 - j
                val j0 : g1uint (tk, j0) = pred num_piles - j

                val [last_elems_j0 : int]
                    last_elems_j0 = last_elems[j0]
                val () =
                  $effmask_exn assertloc (last_elems_j0 <> g1u2u 0u)

                stadef i1 = q - 1
                stadef i2 = last_elems_j0 - 1
                val i1 = pred q
                and i2 = pred last_elems_j0

                val () = $effmask_exn assertloc (i1 <> i2)

                prval @(pfelem1, pfelem2, fpf) =
                  array_v_takeout_two
                    {a} {..} {n} {i1, i2} (view@ arr)

                val x1_lt_x2 =
                  (!(ptr_add<a> (addr@ arr, i1)))
                    \lt (!(ptr_add<a> (addr@ arr, i2)))

                prval () = view@ arr := fpf (pfelem1, pfelem2)
              in
                if x1_lt_x2 then
                  succ num_piles
                else
                  g1u2u 1u
              end
          end
        else
          let
            typedef index (i : int) = [0 <= i; i < n] g1uint (tk, i)
            typedef index = [i : int] index i

            stadef i = j + ((k - j) / 2)
            val i : g1uint (tk, i) = j + half (k - j)

            stadef j0 = num_piles - 1 - j
            val j0 : g1uint (tk, j0) = pred num_piles - j

            val [last_elems_j0 : int] last_elems_j0 = last_elems[j0]
            val () =
              $effmask_exn assertloc (last_elems_j0 <> g1u2u 0u)

            stadef i1 = q - 1
            stadef i2 = last_elems_j0 - 1
            val i1 = pred q
            and i2 = pred last_elems_j0

            val () = $effmask_exn assertloc (i1 <> i2)

            prval @(pfelem1, pfelem2, fpf) =
              array_v_takeout_two {a} {..} {n} {i1, i2} (view@ arr)

            val x1_lt_x2 =
              (!(ptr_add<a> (addr@ arr, i1)))
                \lt (!(ptr_add<a> (addr@ arr, i2)))

            prval () = view@ arr := fpf (pfelem1, pfelem2)
          in
            if x1_lt_x2 then
              loop (arr, last_elems, succ i, k)
            else
              loop (arr, last_elems, j, i)
          end
    in
      loop (arr, last_elems, g1u2u 0u, pred num_piles)
    end

implement {a} {tk}
patience_sort_deal_refparams
          {n} {n_workspace} (arr, n, piles, links, workspace) =
  (*

    I borrow, from the following paper, the trick of building on both
    sides of a pile:

      Badrish Chandramouli and Jonathan Goldstein, ‘Patience is a
        virtue: revisiting merge and sort on modern processors’,
        SIGMOD ’14: Proceedings of the 2014 ACM SIGMOD International
        Conference on Management of Data, June 2014, 731–742.
        https://doi.org/10.1145/2588555.2593662

    Dealing is done backwards through the arr array, so an array
    already sorted in the desired order will result in a single pile
    with just consing.

  *)
  let
    prval () = lemma_g1uint_param n

    typedef link_t (i : int) = link_t (tk, n, i)
    typedef link_t = link_t (tk, n)

    val zero : g1uint (tk, 0) = g1u2u 0u
    val one : g1uint (tk, 1) = g1u2u 1u
    val link_nil : link_t 0 = g1u2u 0u

    val p_last_elems = addr@ workspace
    and p_tails = ptr_add<link_t> (addr@ workspace, n)
    macdef last_elems = !p_last_elems
    macdef tails = !p_tails

    prval @(pf_wspace, pf_leftover_space) =
      array_v_split {link_t?} {..} {n_workspace} {n + n}
                    (view@ workspace)
    val () = array_initize_elt<link_t> (!(addr@ workspace),
                                        g1u2u (n + n), link_nil)
    prval @(pf_last_elems, pf_tails) =
      array_v_split {link_t} {..} {n + n} {n} pf_wspace

    fun
    loop {q             : nat | q <= n}
         {m             : nat | m <= n}
         {p_last_elems  : addr}
         {p_tails       : addr}
         .<q>.
         (pf_last_elems : !array_v (link_t, p_last_elems, n) >> _,
          pf_tails      : !array_v (link_t, p_tails, n) >> _ |
          arr           : &RD(array (a, n)),
          q             : g1uint (tk, q),
          piles         : &array (link_t, n) >> _,
          links         : &array (link_t, n) >> _,
          p_last_elems  : ptr p_last_elems,
          p_tails       : ptr p_tails,
          m             : g1uint (tk, m))
        :<!wrt> [num_piles : nat | num_piles <= n]
                g1uint (tk, num_piles) =
      if q = zero then
        m
      else
        let
          macdef last_elems = !p_last_elems
          macdef tails = !p_tails

          val i = find_pile<a><tk> {n} (arr, m, piles, q)

          (* We have no proof the number of elements will not exceed
             storage. However, we know it will not, because the number
             of piles cannot exceed the size of the input. Let us get
             a "proof" by runtime check. *)
          val () = $effmask_exn assertloc (i <= n)
        in
          if i = succ m then
            let
              val i =
                find_last_elem<a><tk> {n} (arr, m, last_elems, q)
              val () = $effmask_exn assertloc (i <= n)
            in
              if i = succ m then
                begin           (* Start a new pile. *)
                  piles[pred i] := q;
                  last_elems[pred i] := q;
                  tails[pred i] := q;
                  loop (pf_last_elems, pf_tails |
                        arr, pred q, piles, links,
                        p_last_elems, p_tails, succ m)
                end
              else
                let             (* Append to the end of a pile. *)
                  val i0 = tails[pred i]
                  val () = $effmask_exn assertloc (i0 <> g1u2u 0u)
                in
                  links[pred i0] := q;
                  last_elems[pred i] := q;
                  tails[pred i] := q;
                  loop (pf_last_elems, pf_tails |
                        arr, pred q, piles, links,
                        p_last_elems, p_tails, m)
                end
            end
          else
            begin             (* Cons onto the beginning of a pile. *)
              links[pred q] := piles[pred i];
              piles[pred i] := q;
              loop (pf_last_elems, pf_tails |
                    arr, pred q, piles, links,
                    p_last_elems, p_tails, m)
            end
        end

    val () = array_initize_elt<link_t> (piles, g1u2u n, link_nil)
    val () = array_initize_elt<link_t> (links, g1u2u n, link_nil)

    val num_piles = loop (pf_last_elems, pf_tails |
                          arr, n, piles, links,
                          p_last_elems, p_tails, zero)

    prval pf_wspace = array_v_unsplit (pf_last_elems, pf_tails)
    prval () = array_v_uninitize_without_doing_anything pf_wspace
    prval () = view@ workspace :=
      array_v_unsplit (pf_wspace, pf_leftover_space)
  in
    num_piles
  end

implement {a} {tk}
patience_sort_deal_valparams
          (pf_piles, pf_links, pf_workspace |
           n, arr, p_piles, p_links, p_workspace) =
  patience_sort_deal_refparams<a><tk> (n, arr, !p_piles, !p_links,
                                       !p_workspace)

fn {a  : vt@ype}
   {tk : tkind}
k_way_merge_refparams
          {n         : int}
          {num_piles : pos | num_piles <= n}
          {power     : int | num_piles <= power}
          {n_indices : int | n_indices == n || n_indices == 0}
          {n_elems   : int | n_elems == n || n_elems == 0;
                             n_indices == 0 || n_elems == 0}
          (pf_exp2   : [exponent : nat] EXP2 (exponent, power) |
           arr       : &RD(array (a, n)),
           n         : g1uint (tk, n),
           num_piles : g1uint (tk, num_piles),
           power     : g1uint (tk, power),
           piles     : &array (link_t (tk, n), n) >> _,
           links     : &RD(array (link_t (tk, n), n)),
           winners   : &array (link_t (tk, n)?, 4 * power) >> _,
           indices   : &array (index_t (tk, n)?, n_indices)
                       >> array (index_t (tk, n), n_indices),
           n_indices : g1uint (tk, n_indices),
           elements  : &array (a?, n_elems) >> array (a, n_elems),
           n_elems   : g1uint (tk, n_elems))
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
    val zero : g1uint (tk, 0) = g1u2u 0u
    val one : g1uint (tk, 1) = g1u2u 1u
    val two : g1uint (tk, 2) = g1u2u 2u

    prval () = lemma_g1uint_param n

    typedef link_t (i : int) = link_t (tk, n, i)
    typedef link_t = link_t (tk, n)

    val link_nil : link_t 0 = zero

    typedef index_t (i : int) = index_t (tk, n, i)
    typedef index_t = index_t (tk, n)

    val [total_external_nodes : int]
        @(_ | total_external_nodes) = next_power_of_two num_piles
    prval () = prop_verify {num_piles <= total_external_nodes} ()

    stadef total_nodes = (2 * total_external_nodes) - 1
    val total_nodes : g1uint (tk, total_nodes) =
      pred (g1u2u 2u * total_external_nodes)

    (* We will ignore index 0 of the winners tree arrays. *)
    stadef winners_size = total_nodes + 1
    val winners_size : g1uint (tk, winners_size) = succ total_nodes

    (* An exercise for the reader is to write a proof that
       winners_size <= 2 * power, so one can get rid of the
       runtime assertion here: *)
    val () = $effmask_exn assertloc (winners_size <= two * power)

    prval @(winners_left, winners_right) =
      array_v_split {link_t?} {..} {4 * power} {2 * winners_size}
                    (view@ winners)
    prval () = view@ winners := winners_left

    val () =
      array_initize_elt<link_t> (winners, g1u2u (two * winners_size),
                                 link_nil)

    #define VALUE 0
    #define LINK  1

    typedef winners_field_t (i : int) =
      [i : int | i == VALUE || i == LINK]
      int i
    typedef winners_field_t =
      [i : int] winners_field_t i

    fn {}
    winners_get {i       : int | i < winners_size}
                (winners : &RD(array (link_t, 2 * winners_size)),
                 field   : winners_field_t,
                 i       : g1uint (tk, i))
        :<> link_t (tk, n) =
      let
        prval () = lemma_g1uint_param i
      in
        winners[i + i + g1i2u field]
      end

    fn {}
    winners_set {i       : int | i < winners_size}
                (winners : &array (link_t, 2 * winners_size) >> _,
                 field   : winners_field_t,
                 i       : g1uint (tk, i),
                 x       : link_t)
        :<!wrt> void =
      let
        prval () = lemma_g1uint_param i
      in
        winners[i + i + g1i2u field] := x
      end

    overload [] with winners_get of 1000
    overload [] with winners_set of 1000

    (* - - - - - - - - - - - - - - - - - - - - - - - - - - *)
    (* The top of each pile becomes a starting competitor. *)
    (* The LINK field tells which pile a winner will have  *)
    (* come from.                                          *)

    fun
    init_competitors
              {i : nat | i <= num_piles}
              .<num_piles - i>.
              (winners : &array (link_t, 2 * winners_size),
               piles   : &array (link_t, n),
               i       : g1uint (tk, i))
        :<!wrt> void =
      if i <> num_piles then
        begin
          winners[VALUE, total_external_nodes + i] := piles[i];
          winners[LINK, total_external_nodes + i] := succ i;
          init_competitors (winners, piles, succ i)
        end
 
    val () = init_competitors (winners, piles, zero)

    (* - - - - - - - - - - - - - - - - - - - - - - - - - - *)
    (* Discard the top of each pile.                       *)

    fun
    discard_tops {i : nat | i <= num_piles}
                 .<num_piles - i>.
                 (piles : &array (link_t, n),
                  links : &array (link_t, n),
                  i     : g1uint (tk, i))
        :<!wrt> void =
      if i <> num_piles then
        let
          val link = piles[i]

          (* None of the piles should have been empty. *)
          val () = $effmask_exn assertloc (link <> link_nil)
        in
          piles[i] := links[pred link];
          discard_tops (piles, links, succ i)
        end

    val () = discard_tops (piles, links, zero)

    (* - - - - - - - - - - - - - - - - - - - - - - - - - - *)
    (* How to play a game.                                 *)
    
    fn
    find_opponent {i : int | 2 <= i; i <= total_nodes}
                  (i : g1uint (tk, i))
        :<> [j : int | 2 <= j; j <= total_nodes]
            g1uint (tk, j) =
      let
        (* The prelude contains bitwise operations only for
           non-dependent unsigned integer. We will not bother to
           add them ourselves, but instead go back and forth
           between dependent and non-dependent. *)
        val i0 = g0ofg1 i
        val j0 = g0uint_lxor<tk> (i0, g0u2u 1u)
        val j = g1ofg0 j0

        (* We have no proof the opponent is in the proper
           range. Create a "proof" by runtime checks. *)
        val () = $effmask_exn assertloc (g1u2u 2u <= j)
        val () = $effmask_exn assertloc (j <= total_nodes)
      in
        j
      end

    fn
    play_game {i, j     : int | 2 <= i; i <= total_nodes;
                                2 <= j; j <= total_nodes}
              {winner_i : int}
              {winner_j : int}
              (arr      : &RD(array (a, n)),
               i        : g1uint (tk, i),
               j        : g1uint (tk, j),
               winner_i : link_t winner_i,
               winner_j : link_t winner_j)
        :<> [iwinner : pos | iwinner <= total_nodes]
            g1uint (tk, iwinner) =
      let
        macdef lt = patience_sort$lt<a>
      in
        if winner_i = link_nil then
          j
        else if winner_j = link_nil then
          i
        else
          let
            stadef i1 = winner_i - 1
            stadef i2 = winner_j - 1
            val i1 = pred winner_i
            and i2 = pred winner_j
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
                winners  : &array (link_t, 2 * winners_size),
                istart   : g1uint (tk, istart))
        :<!wrt> void =
      if istart <> one then
        let
          fun
          play_initial_games
                    {i : int | istart <= i; i <= (2 * istart) + 1}
                    .<(2 * istart) + 1 - i>.
                    (arr      : &RD(array (a, n)),
                     winners  : &array (link_t, 2 * winners_size),
                     i        : g1uint (tk, i))
              :<!wrt> void =
            if i <= pred (istart + istart) then
              let
                val winner_i = winners[VALUE, i]
              in
                if winner_i = link_nil then
                  ()     (* Leave the loop immediately, if there is no
                            competitor. *)
                else          
                  let
                    val j = find_opponent i
                    val winner_j = winners[VALUE, j]
                    val iwinner =
                      play_game (arr, i, j, winner_i, winner_j)
                    and i2 = half i
                  in
                    winners[VALUE, i2] := winners[VALUE, iwinner];
                    winners[LINK, i2] := winners[LINK, iwinner];
                    if winner_j = link_nil then
                      () (* Leave the loop immediately, if there is no
                            opponent. *)
                    else
                      play_initial_games (arr, winners, succ (succ i))
                  end
              end
        in
          play_initial_games (arr, winners, istart);
          build_tree (arr, winners, half istart)
        end

    val () = build_tree (arr, winners, total_external_nodes)

    (* - - - - - - - - - - - - - - - - - - - - - - - - - - *)

    fun
    replay_games {i : pos | i <= total_nodes}
                 .<i>.
                 (arr      : &RD(array (a, n)),
                  winners  : &array (link_t, 2 * winners_size),
                  i        : g1uint (tk, i))
        :<!wrt> void =
      if i <> g1u2u 1u then
        let
          val j = find_opponent i
          val iwinner = play_game (arr, i, j, winners[VALUE, i],
                                   winners[VALUE, j])
          and i2 = half i
        in
          winners[VALUE, i2] := winners[VALUE, iwinner];
          winners[LINK, i2] := winners[LINK, iwinner];
          replay_games (arr, winners, i2)
        end

    fun
    merge_to_indices
              {isorted    : nat | isorted <= n}
              {p_indices  : addr}
              .<n - isorted>.
              (pf_indices : !array_v (index_t?, p_indices,
                                      n - isorted)
                            >> array_v (index_t, p_indices,
                                        n - isorted) |
               arr        : &RD(array (a, n)),
               piles      : &array (link_t, n),
               links      : &array (link_t, n),
               winners    : &array (link_t, 2 * winners_size),
               p_indices  : ptr p_indices,
               isorted    : g1uint (tk, isorted))
        :<!wrt> void =
      if isorted <> n then
        let
          prval @(pf_elem, pf_rest) = array_v_uncons pf_indices
          val winner = winners[VALUE, g1u2u 1u]
          val () = $effmask_exn assertloc (winner <> link_nil)
          val () = !p_indices := pred winner

          (* Move to the next element in the winner's pile. *)
          val ilink = winners[LINK, g1u2u 1u]
          val () = $effmask_exn assertloc (ilink <> link_nil)
          val inext = piles[pred ilink]
          val () = (if inext <> link_nil then
                      piles[pred ilink] := links[pred inext])

          (* Replay games, with the new element as a competitor. *)
          val i = half total_nodes + ilink
          val () = $effmask_exn assertloc (i <= total_nodes)
          val () = winners[VALUE, i] := inext
          val () = replay_games (arr, winners, i)

          val () =
            merge_to_indices
              (pf_rest |
               arr, piles, links, winners, ptr_succ<index_t> p_indices,
               succ isorted)

          prval () = pf_indices := array_v_cons (pf_elem, pf_rest)
        in
        end
      else
        let
          prval () = pf_indices :=
            array_v_unnil_nil{index_t?, index_t} pf_indices
        in
        end

    fun
    merge_to_elements
              (* The "arr" array really should have its element
                 type changed to "a?!". We will do that in the
                 publicly available routine instead of here. *)
              {isorted  : nat | isorted <= n}
              {p_elems  : addr}
              .<n - isorted>.
              (pf_elems : !array_v (a?, p_elems, n - isorted)
                          >> array_v (a, p_elems, n - isorted) |
               arr      : &RD(array (a, n)),
               piles    : &array (link_t, n),
               links    : &array (link_t, n),
               winners  : &array (link_t, 2 * winners_size),
               p_elems  : ptr p_elems,
               isorted  : g1uint (tk, isorted))
        :<!wrt> void =
      if isorted <> n then
        let
          prval @(pf_elem, pf_rest) = array_v_uncons pf_elems
          val winner = winners[VALUE, g1u2u 1u]
          val () = $effmask_exn assertloc (winner <> link_nil)
          val () = !p_elems :=
            $UN.ptr0_get<a> (ptr_add<a> (addr@ arr, pred winner))

          (* Move to the next element in the winner's pile. *)
          val ilink = winners[LINK, g1u2u 1u]
          val () = $effmask_exn assertloc (ilink <> link_nil)
          val inext = piles[pred ilink]
          val () = (if inext <> link_nil then
                      piles[pred ilink] := links[pred inext])

          (* Replay games, with the new element as a competitor. *)
          val i = half total_nodes + ilink
          val () = $effmask_exn assertloc (i <= total_nodes)
          val () = winners[VALUE, i] := inext
          val () = replay_games (arr, winners, i)

          val () =
            merge_to_elements
              (pf_rest |
               arr, piles, links, winners, ptr_succ<a> p_elems,
               succ isorted)

          prval () = pf_elems := array_v_cons (pf_elem, pf_rest)
        in
        end
      else
        let
          prval () = pf_elems := array_v_unnil_nil{a?, a} pf_elems
        in
        end
  in
    if n_indices = zero then
      let
        prval () = view@ indices :=
          array_v_unnil_nil{index_t?, index_t} (view@ indices)
      in
        if n_elems = zero then
          let
            prval () = view@ elements :=
              array_v_unnil_nil{a?, a} (view@ elements)

            prval () =
              array_v_uninitize_without_doing_anything (view@ winners)
            prval () = view@ winners :=
              array_v_unsplit (view@ winners, winners_right)
          in
          end
        else
          let
            val () =
              merge_to_elements
                (view@ elements |
                 arr, piles, links, winners, addr@ elements, zero)

            prval () =
              array_v_uninitize_without_doing_anything (view@ winners)
            prval () = view@ winners :=
              array_v_unsplit (view@ winners, winners_right)
          in
          end
      end
    else
      let
        val () =
          merge_to_indices
            (view@ indices |
             arr, piles, links, winners, addr@ indices, zero)

        prval () = view@ elements :=
          array_v_unnil_nil{a?, a} (view@ elements)

        prval () =
          array_v_uninitize_without_doing_anything (view@ winners)
        prval () = view@ winners :=
          array_v_unsplit (view@ winners, winners_right)
      in
      end
  end

fn {a  : vt@ype}
   {tk : tkind}
k_way_merge_valparams
          {n           : int}
          {num_piles   : pos | num_piles <= n}
          {power       : int | num_piles <= power}
          {n_indices   : int | n_indices == n || n_indices == 0}
          {n_elems     : int | n_elems == n || n_elems == 0;
                               n_indices == 0 || n_elems == 0}
          {p_piles     : addr}
          {p_links     : addr}
          {p_winners   : addr}
          (pf_exp2     : [exponent : nat] EXP2 (exponent, power),
           pf_piles    : !array_v (link_t (tk, n), p_piles, n)
                         >> _,
           pf_links    : !array_v (link_t (tk, n), p_links, n)
                         >> _,
           pf_winners  : !array_v (link_t (tk, n)?, p_winners,
                                   4 * power) >> _ |
           arr         : &RD(array (a, n)),
           n           : g1uint (tk, n),
           num_piles   : g1uint (tk, num_piles),
           power       : g1uint (tk, power),
           p_piles     : ptr p_piles,
           p_links     : ptr p_links,
           p_winners   : ptr p_winners,
           indices     : &array (index_t (tk, n)?, n_indices)
                         >> array (index_t (tk, n), n_indices),
           n_indices   : g1uint (tk, n_indices),
           elements    : &array (a?, n_elems) >> array (a, n_elems),
           n_elems     : g1uint (tk, n_elems))
    :<!wrt> void =
  k_way_merge_refparams<a><tk>
    (pf_exp2 |
     arr, n, num_piles, power, !p_piles, !p_links, !p_winners,
     indices, n_indices, elements, n_elems)

implement {a} {tk}
patience_sort_merge_to_indices_refparams
          (pf_exp2 |
           arr, n, num_piles, power, piles, links,
           workspace, indices) =
  patience_sort_merge_to_indices_valparams<a><tk>
    (pf_exp2, view@ piles, view@ links, view@ workspace |
     arr, n, num_piles, power,
     addr@ piles, addr@ links, addr@ workspace, indices)

implement {a} {tk}
patience_sort_merge_to_indices_valparams
          {n} {num_piles} {power} {n_workspace}
          {p_piles} {p_links} {p_workspace}
          (pf_exp2, pf_piles, pf_links, pf_workspace |
           arr, n, num_piles, power, p_piles, p_links,
           p_workspace, indices) =
  let
    typedef link_t = link_t (tk, n)

    prval @(pf_winners, pf_rest) =
      array_v_split {link_t?} {p_workspace} {n_workspace} {4 * power}
                    pf_workspace

    var elements : array (a, 0)

    val p_winners = p_workspace
    val () =
      k_way_merge_valparams<a><tk>
        (pf_exp2, pf_piles, pf_links, pf_winners |
         arr, n, num_piles, power, p_piles, p_links, p_winners,
         indices, n, elements, g1u2u 0u)

    prval () = view@ elements :=
      array_v_unnil_nil{a, a?} (view@ elements)

    prval () = pf_workspace := array_v_unsplit (pf_winners, pf_rest)
  in
  end

implement {a} {tk}
patience_sort_merge_to_elements_refparams
          (pf_exp2 |
           arr, n, num_piles, power, piles, links,
           workspace, elements) =
  patience_sort_merge_to_elements_valparams<a><tk>
    (pf_exp2, view@ piles, view@ links, view@ workspace |
     arr, n, num_piles, power,
     addr@ piles, addr@ links, addr@ workspace, elements)

implement {a} {tk}
patience_sort_merge_to_elements_valparams
          {n} {num_piles} {power} {n_workspace}
          {p_piles} {p_links} {p_workspace}
          (pf_exp2, pf_piles, pf_links, pf_workspace |
           arr, n, num_piles, power, p_piles, p_links,
           p_workspace, elements) =
  let
    typedef index_t = index_t (tk, n)
    typedef link_t = link_t (tk, n)

    prval @(pf_winners, pf_rest) =
      array_v_split {link_t?} {p_workspace} {n_workspace} {4 * power}
                    pf_workspace

    var indices : array (index_t, 0)

    val p_winners = p_workspace
    val () =
      k_way_merge_valparams<a><tk>
        (pf_exp2, pf_piles, pf_links, pf_winners |
         arr, n, num_piles, power, p_piles, p_links, p_winners,
         indices, g1u2u 0u, elements, n)

    prval () = view@ indices :=
      array_v_unnil_nil{index_t, index_t?} (view@ indices)

    prval () = pf_workspace := array_v_unsplit (pf_winners, pf_rest)

    prval () = $UN.castview2void_at{array (a?!, n)} (view@ arr)
  in
  end

(* ================================================================ *)
(* Interfaces that provides workspace. If the subarray to be sorted *)
(* is ‘small enough’, stack storage will be used.                   *)

#define LEN_THRESHOLD   128
#define PILES_SIZE      128
#define LINKS_SIZE      128
#define WORKSPACE_SIZE  512

prval () = prop_verify {PILES_SIZE == LEN_THRESHOLD} ()
prval () = prop_verify {LINKS_SIZE == LEN_THRESHOLD} ()
prval () = prop_verify {WORKSPACE_SIZE == 4 * LEN_THRESHOLD} ()

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

(* ---------------------------------------------------------------- *)

implement {a} {tk}
patience_sort_into_indices_array
          {n} (arr, n, indices) =
  let
    val zero : g1uint (tk, 0) = g1u2u 0u
    val two : g1uint (tk, 2) = g1u2u 2u
    val four : g1uint (tk, 4) = g1u2u 4u

    prval () = lemma_g1uint_param n

    typedef index_t = index_t (tk, n)
    typedef link_t = link_t (tk, n)

    fn
    deal {n_workspace : int | 2 * n <= n_workspace}
         {p_piles     : addr}
         {p_links     : addr}
         {p_workspace : addr}
         (pf_piles    : !array_v (link_t?, p_piles, n)
                        >> array_v (link_t, p_piles, n),
          pf_links    : !array_v (link_t?, p_links, n)
                        >> array_v (link_t, p_links, n),
          pf_workspace : !array_v (link_t?, p_workspace,
                                   n_workspace) >> _ |
          n           : g1uint (tk, n),
          arr         : &RD(array (a, n)),
          p_piles     : ptr p_piles,
          p_links     : ptr p_links,
          p_workspace : ptr p_workspace)
        :<!wrt> [num_piles : int | num_piles <= n]
                g1uint (tk, num_piles) =
      patience_sort_deal<a><tk>
        (pf_piles, pf_links, pf_workspace |
         arr, n, p_piles, p_links, p_workspace)

    fn
    merge {num_piles    : pos | num_piles <= n}
          {power        : int | num_piles <= power}
          {n_workspace  : int | 4 * power <= n_workspace}
          {p_piles      : addr}
          {p_links      : addr}
          {p_workspace  : addr}
          (pf_exp2      : [exponent : nat] EXP2 (exponent, power),
           pf_piles     : !array_v (link_t, p_piles, n) >> _,
           pf_links     : !array_v (link_t, p_links, n) >> _,
           pf_workspace : !array_v (link_t?, p_workspace,
                                    n_workspace) >> _ |
           arr          : &RD(array (a, n)),
           n            : g1uint (tk, n),
           num_piles    : g1uint (tk, num_piles),
           power        : g1uint (tk, power),
           p_piles      : ptr p_piles,
           p_links      : ptr p_links,
           p_workspace  : ptr p_workspace,
           indices      : &array (index_t?, n)
                            >> array (index_t, n))
        :<!wrt> void =
      patience_sort_merge_to_indices<a><tk>
        (pf_exp2, pf_piles, pf_links, pf_workspace |
         arr, n, num_piles, power, p_piles, p_links,
         p_workspace, indices)
  in
    if n = zero then
      let
        prval () = view@ indices :=
          array_v_unnil_nil{index_t?, index_t} (view@ indices)
      in
      end
    else if n <= g1i2u LEN_THRESHOLD then
      (* Use stack storage. *)
      let
        var piles : array (link_t, PILES_SIZE)
        var links : array (link_t, LINKS_SIZE)
        var workspace : array (link_t, WORKSPACE_SIZE)

        prval @(pf_piles, pf_piles_rest) =
          array_v_split {link_t?} {..} {PILES_SIZE} {n}
                        (view@ piles)
        prval @(pf_links, pf_links_rest) =
          array_v_split {link_t?} {..} {LINKS_SIZE} {n}
                        (view@ links)

        val num_piles =
          deal (pf_piles, pf_links, view@ workspace |
                n, arr, addr@ piles, addr@ links, addr@ workspace)

        prval () = lemma_g1uint_param num_piles
        val () = $effmask_exn assertloc (num_piles <> zero)

        prval pf_exp2 = pf_exp2_for_stack_storage
        val power = g1i2u LEN_THRESHOLD

        val () =
          merge (pf_exp2, pf_piles, pf_links, view@ workspace |
                 arr, n, num_piles, power,
                 addr@ piles, addr@ links, addr@ workspace, indices)

        prval () = array_v_uninitize_without_doing_anything pf_piles
        prval () = array_v_uninitize_without_doing_anything pf_links

        prval () = view@ piles :=
          array_v_unsplit (pf_piles, pf_piles_rest)
        prval () = view@ links :=
          array_v_unsplit (pf_links, pf_links_rest)
      in
      end
    else
      (* Use malloc storage. *)
      let
        val @(pf_piles, pfgc_piles | p_piles) =
          array_ptr_alloc<link_t> (g1u2u n)
        val @(pf_links, pfgc_links | p_links) =
          array_ptr_alloc<link_t> (g1u2u n)

        val @(pf_workspace, pfgc_workspace | p_workspace) =
          array_ptr_alloc<link_t> (g1u2u (two * n))

        val num_piles =
          deal (pf_piles, pf_links, pf_workspace |
                n, arr, p_piles, p_links, p_workspace)

        prval () = lemma_g1uint_param num_piles
        val () = $effmask_exn assertloc (num_piles <> zero)

        val @(pf_exp2 | power) = next_power_of_two<tk> num_piles
      in
        if four * power <= two * g1u2u n then
          begin
            merge (pf_exp2, pf_piles, pf_links, pf_workspace |
                   arr, n, num_piles, power,
                   p_piles, p_links, p_workspace, indices);

            array_ptr_free (pf_piles, pfgc_piles | p_piles);
            array_ptr_free (pf_links, pfgc_links | p_links);
            array_ptr_free (pf_workspace, pfgc_workspace |
                            p_workspace)
          end
        else
          let
            val () = array_ptr_free (pf_workspace, pfgc_workspace |
                                     p_workspace)
            val @(pf_workspace, pfgc_workspace | p_workspace) =
              array_ptr_alloc<link_t> (g1u2u (four * power))
          in
            merge (pf_exp2, pf_piles, pf_links, pf_workspace |
                   arr, n, num_piles, power,
                   p_piles, p_links, p_workspace, indices);

            array_ptr_free (pf_piles, pfgc_piles | p_piles);
            array_ptr_free (pf_links, pfgc_links | p_links);
            array_ptr_free (pf_workspace, pfgc_workspace |
                            p_workspace)
          end
      end
  end

(* ---------------------------------------------------------------- *)

implement {a} {tk}
patience_sort_into_elements_array {n} (arr, n, elements) =
  let
    val zero : g1uint (tk, 0) = g1u2u 0u
    val two : g1uint (tk, 2) = g1u2u 2u
    val four : g1uint (tk, 4) = g1u2u 4u

    prval () = lemma_g1uint_param n

    typedef index_t = index_t (tk, n)
    typedef link_t = link_t (tk, n)

    fn
    deal {n_workspace : int | 2 * n <= n_workspace}
         {p_piles     : addr}
         {p_links     : addr}
         {p_workspace : addr}
         (pf_piles    : !array_v (link_t?, p_piles, n)
                        >> array_v (link_t, p_piles, n),
          pf_links    : !array_v (link_t?, p_links, n)
                        >> array_v (link_t, p_links, n),
          pf_workspace : !array_v (link_t?, p_workspace,
                                   n_workspace) >> _ |
          n           : g1uint (tk, n),
          arr         : &RD(array (a, n)),
          p_piles     : ptr p_piles,
          p_links     : ptr p_links,
          p_workspace : ptr p_workspace)
        :<!wrt> [num_piles : int | num_piles <= n]
                g1uint (tk, num_piles) =
      patience_sort_deal<a><tk>
        (pf_piles, pf_links, pf_workspace |
         arr, n, p_piles, p_links, p_workspace)

    fn
    merge {num_piles    : pos | num_piles <= n}
          {power        : int | num_piles <= power}
          {n_workspace  : int | 4 * power <= n_workspace}
          {p_piles      : addr}
          {p_links      : addr}
          {p_workspace  : addr}
          (pf_exp2      : [exponent : nat] EXP2 (exponent, power),
           pf_piles     : !array_v (link_t, p_piles, n) >> _,
           pf_links     : !array_v (link_t, p_links, n) >> _,
           pf_workspace : !array_v (link_t?, p_workspace,
                                    n_workspace) >> _ |
           arr          : &array (a, n) >> array (a?!, n),
           n            : g1uint (tk, n),
           num_piles    : g1uint (tk, num_piles),
           power        : g1uint (tk, power),
           p_piles      : ptr p_piles,
           p_links      : ptr p_links,
           p_workspace  : ptr p_workspace,
           elements     : &array (a?, n) >> array (a, n))
        :<!wrt> void =
      patience_sort_merge_to_elements<a><tk>
        (pf_exp2, pf_piles, pf_links, pf_workspace |
         arr, n, num_piles, power, p_piles, p_links,
         p_workspace, elements)
  in
    if n = zero then
      let
        prval () = view@ elements :=
          array_v_unnil_nil{a?, a} (view@ elements)
        prval () = $UN.castview2void_at{array (a?!, n)} (view@ arr)
      in
      end
    else if n <= g1i2u LEN_THRESHOLD then
      (* Use stack storage. *)
      let
        var piles : array (link_t, PILES_SIZE)
        var links : array (link_t, LINKS_SIZE)
        var workspace : array (link_t, WORKSPACE_SIZE)

        prval @(pf_piles, pf_piles_rest) =
          array_v_split {link_t?} {..} {PILES_SIZE} {n}
                        (view@ piles)
        prval @(pf_links, pf_links_rest) =
          array_v_split {link_t?} {..} {LINKS_SIZE} {n}
                        (view@ links)

        val num_piles =
          deal (pf_piles, pf_links, view@ workspace |
                n, arr, addr@ piles, addr@ links, addr@ workspace)

        prval () = lemma_g1uint_param num_piles
        val () = $effmask_exn assertloc (num_piles <> zero)

        prval pf_exp2 = pf_exp2_for_stack_storage
        val power = g1i2u LEN_THRESHOLD

        val () =
          merge (pf_exp2, pf_piles, pf_links, view@ workspace |
                 arr, n, num_piles, power,
                 addr@ piles, addr@ links, addr@ workspace, elements)

        prval () = array_v_uninitize_without_doing_anything pf_piles
        prval () = array_v_uninitize_without_doing_anything pf_links

        prval () = view@ piles :=
          array_v_unsplit (pf_piles, pf_piles_rest)
        prval () = view@ links :=
          array_v_unsplit (pf_links, pf_links_rest)
      in
      end
    else
      (* Use malloc storage. *)
      let
        val @(pf_piles, pfgc_piles | p_piles) =
          array_ptr_alloc<link_t> (g1u2u n)
        val @(pf_links, pfgc_links | p_links) =
          array_ptr_alloc<link_t> (g1u2u n)

        val @(pf_workspace, pfgc_workspace | p_workspace) =
          array_ptr_alloc<link_t> (g1u2u (two * n))

        val num_piles =
          deal (pf_piles, pf_links, pf_workspace |
                n, arr, p_piles, p_links, p_workspace)

        prval () = lemma_g1uint_param num_piles
        val () = $effmask_exn assertloc (num_piles <> zero)

        val @(pf_exp2 | power) = next_power_of_two<tk> num_piles
      in
        if four * power <= two * g1u2u n then
          begin
            merge (pf_exp2, pf_piles, pf_links, pf_workspace |
                   arr, n, num_piles, power,
                   p_piles, p_links, p_workspace, elements);

            array_ptr_free (pf_piles, pfgc_piles | p_piles);
            array_ptr_free (pf_links, pfgc_links | p_links);
            array_ptr_free (pf_workspace, pfgc_workspace |
                            p_workspace)
          end
        else
          let
            val () = array_ptr_free (pf_workspace, pfgc_workspace |
                                     p_workspace)
            val @(pf_workspace, pfgc_workspace | p_workspace) =
              array_ptr_alloc<link_t> (g1u2u (four * power))
          in
            merge (pf_exp2, pf_piles, pf_links, pf_workspace |
                   arr, n, num_piles, power,
                   p_piles, p_links, p_workspace, elements);

            array_ptr_free (pf_piles, pfgc_piles | p_piles);
            array_ptr_free (pf_links, pfgc_links | p_links);
            array_ptr_free (pf_workspace, pfgc_workspace |
                            p_workspace)
          end
      end
  end

(* ---------------------------------------------------------------- *)

implement {a} {tk}
patience_sort_returning_elements_array {n} (arr, n) =
  let

    prval () = lemma_array_param arr
    prval () = prop_verify {0 <= n} ()

    fn
    sort (arr      : &array (a, n) >> array (a?!, n),
          elements : &array (a?, n) >> array (a, n))
        :<!wrt> void =
      patience_sort_into_elements_array<a><tk> (arr, n, elements)
  in
    let
      val retval = array_ptr_alloc<a> (g1u2u n)
      macdef elements = !(retval.2)
      val () = sort (arr, elements)
    in
      retval
    end
  end

(* ================================================================ *)
