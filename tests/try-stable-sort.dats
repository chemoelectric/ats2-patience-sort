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

#include "share/atspre_staload.hats"
#include "patience-sort/HATS/patience-sort.hats"
staload UN = "prelude/SATS/unsafe.sats"

(*------------------------------------------------------------------*)
(* A simple linear congruential generator.                          *)

(* The multiplier lcg_a comes from Steele, Guy; Vigna, Sebastiano (28
   September 2021). "Computationally easy, spectrally good multipliers
   for congruential pseudorandom number generators".
   arXiv:2001.05304v3 [cs.DS] *)
macdef lcg_a = $UN.cast{uint64} 0xf1357aea2e62a9c5LLU

(* lcg_c must be odd. *)
macdef lcg_c = $UN.cast{uint64} 0xbaceba11beefbeadLLU

var seed : uint64 = $UN.cast 0
val p_seed = addr@ seed

fn
random_double () :<!wrt> double =
  let
    val (pf, fpf | p_seed) = $UN.ptr0_vtake{uint64} p_seed
    val old_seed = ptr_get<uint64> (pf | p_seed)

    (* IEEE "binary64" or "double" has 52 bits of precision. We will
       take the high 48 bits of the seed and divide it by 2**48, to
       get a number 0.0 <= randnum < 1.0 *)
    val high_48_bits = $UN.cast{double} (old_seed >> 16)
    val divisor = $UN.cast{double} (1LLU << 48)
    val randnum = high_48_bits / divisor

    (* The following operation is modulo 2**64, by virtue of standard
       C behavior for uint64_t. *)
    val new_seed = (lcg_a * old_seed) + lcg_c

    val () = ptr_set<uint64> (pf | p_seed, new_seed)
    prval () = fpf pf
  in
    randnum
  end

fn
random_int (m : int, n : int) :<!wrt> int =
  m + $UN.cast{int} (random_double () * (n - m + 1))

(*------------------------------------------------------------------*)

fn {a  : t@ype}
   {tk : tkind}
find_length {n   : int}
            (lst : list (a, n))
    :<> [m : int | m == n] g1uint (tk, m) =
  let
    prval () = lemma_list_param lst
  in
    g1i2u (length lst)
  end

fn
find_first_letter {n            : int}
                  (n            : size_t n,
                   words_copy   : &RD(array (string, n)),
                   first_letter : char)
    : [i : int | i <= n] size_t i =
  let
    fun
    loop {i          : nat | i <= n}
         (words_copy : &RD(array (string, n)),
          i          : size_t i)
        : [i1 : int | i1 <= n] size_t i1 =
      if i = n then
        i
      else
        let
          val s = g1ofg0 words_copy[i]
        in
          if iseqz s then
            loop (words_copy, succ i)
          else if tolower s[0] <> first_letter then
            loop (words_copy, succ i)
          else
            i
        end

    prval () = lemma_array_param words_copy
  in
    loop (words_copy, i2sz 0)
  end

fn
scramble_words {n               : int}
               (n               : size_t n,
                words           : &RD(array (string, n)),
                scrambled_words : &array (string?, n)
                                  >> array (string, n))
    : void =
  (* Scramble the words, without changing the relative order of words
     that start with the same letter. *)
  let
    fun
    scramble {i_scrambled     : nat | i_scrambled <= n}
             {num_letters     : nat}
             (words_copy      : &array (string, n) >> _,
              scrambled_words : &array (string, n) >> _,
              i_scrambled     : size_t i_scrambled,
              letters         : list (string 1, num_letters),
              num_letters     : int num_letters)
        : void =
      if i_scrambled <> n then
        let
          val i_first_letter =
            g1ofg0 (random_int (0, num_letters - 1))
          val () = assertloc (0 <= i_first_letter)
          val () = assertloc (i_first_letter <= num_letters - 1)
          val first_letter = list_nth (letters, i_first_letter)
          val first_letter = first_letter[0]
          val j = find_first_letter (n, words_copy, first_letter)
        in
          if j <> n then
            let                 (* Move the word. *)
              prval () = lemma_g1uint_param j
            in
              scrambled_words[i_scrambled] := words_copy[j];
              words_copy[j] := "";
              scramble (words_copy, scrambled_words, succ i_scrambled,
                        letters, num_letters)
            end
          else
            let                 (* Remove the letter. *)
            in
              scramble (words_copy, scrambled_words, i_scrambled,
                        list_remove_at (letters, i_first_letter),
                        pred num_letters)
            end
        end

    val @(pf_words_copy, pfgc_words_copy | p_words_copy) =
      array_ptr_alloc<string> n
    macdef words_copy = !p_words_copy
    val () = array_copy<string> (words_copy, words, n)

    val letters : List0 (string 1) =
      $list ("a", "b", "c", "d", "e", "f", "g", "h", "i",
             "j", "k", "l", "m", "n", "o", "p", "q", "r",
             "s", "t", "u", "v", "w", "x", "y", "z")
    val num_letters = length letters

    prval () = lemma_array_param words_copy
  in
    array_initize_elt<string> (scrambled_words, n, "");
    scramble (words_copy, scrambled_words, i2sz 0,
              letters, num_letters);
    array_ptr_free (pf_words_copy, pfgc_words_copy | p_words_copy)
  end

fn
test_stable_sort () : void =
  let
    val words_list =
      $list ("a", "ability", "able", "about", "above", "accept", "according",
"account", "across", "act", "action", "activity", "actually", "add", "address",
"administration", "admit", "adult", "affect", "after", "again", "against", "age",
"agency", "agent", "ago", "agree", "agreement", "ahead", "air", "all", "allow",
"almost", "alone", "along", "already", "also", "although", "always", "American",
"among", "amount", "analysis", "and", "animal", "another", "answer", "any", "anyone",
"anything", "appear", "apply", "approach", "area", "argue", "arm", "around", "arrive",
"art", "article", "artist", "as", "ask", "assume", "at", "attack", "attention",
"attorney", "audience", "author", "authority", "available", "avoid", "away", "baby",
"back", "bad", "bag", "ball", "bank", "bar", "base", "be", "beat", "beautiful",
"because", "become", "bed", "before", "begin", "behavior", "behind", "believe",
"benefit", "best", "better", "between", "beyond", "big", "bill", "billion", "bit",
"black", "blood", "blue", "board", "body", "book", "born", "both", "box", "boy",
"break", "bring", "brother", "budget", "build", "building", "business", "but", "buy",
"by", "call", "camera", "campaign", "can", "cancer", "candidate", "capital", "car",
"card", "care", "career", "carry", "case", "catch", "cause", "cell", "center",
"central", "century", "certain", "certainly", "chair", "challenge", "chance", "change",
"character", "charge", "check", "child", "choice", "choose", "church", "citizen",
"city", "civil", "claim", "class", "clear", "clearly", "close", "coach", "cold",
"collection", "college", "color", "come", "commercial", "common", "community",
"company", "compare", "computer", "concern", "condition", "conference", "Congress",
"consider", "consumer", "contain", "continue", "control", "cost", "could", "country",
"couple", "course", "court", "cover", "create", "crime", "cultural", "culture", "cup",
"current", "customer", "cut", "dark", "data", "daughter", "day", "dead", "deal",
"death", "debate", "decade", "decide", "decision", "deep", "defense", "degree",
"Democrat", "democratic", "describe", "design", "despite", "detail", "determine",
"develop", "development", "die", "difference", "different", "difficult", "dinner",
"direction", "director", "discover", "discuss", "discussion", "disease", "do", "doctor",
"dog", "door", "down", "draw", "dream", "drive", "drop", "drug", "during", "each",
"early", "east", "easy", "eat", "economic", "economy", "edge", "education", "effect",
"effort", "eight", "either", "election", "else", "employee", "end", "energy", "enjoy",
"enough", "enter", "entire", "environment", "environmental", "especially", "establish",
"even", "evening", "event", "ever", "every", "everybody", "everyone", "everything",
"evidence", "exactly", "example", "executive", "exist", "expect", "experience",
"expert", "explain", "eye", "face", "fact", "factor", "fail", "fall", "family", "far",
"fast", "father", "fear", "federal", "feel", "feeling", "few", "field", "fight",
"figure", "fill", "film", "final", "finally", "financial", "find", "fine", "finger",
"finish", "fire", "firm", "first", "fish", "five", "floor", "fly", "focus", "follow",
"food", "foot", "for", "force", "foreign", "forget", "form", "former", "forward",
"four", "free", "friend", "from", "front", "full", "fund", "future", "game", "garden",
"gas", "general", "generation", "get", "girl", "give", "glass", "go", "goal", "good",
"government", "great", "green", "ground", "group", "grow", "growth", "guess", "gun",
"guy", "hair", "half", "hand", "hang", "happen", "happy", "hard", "have", "he", "head",
"health", "hear", "heart", "heat", "heavy", "help", "her", "here", "herself", "high",
"him", "himself", "his", "history", "hit", "hold", "home", "hope", "hospital", "hot",
"hotel", "hour", "house", "how", "however", "huge", "human", "hundred", "husband", "I",
"idea", "identify", "if", "image", "imagine", "impact", "important", "improve", "in",
"include", "including", "increase", "indeed", "indicate", "individual", "industry",
"information", "inside", "instead", "institution", "interest", "interesting",
"international", "interview", "into", "investment", "involve", "issue", "it", "item",
"its", "itself", "job", "join", "just", "keep", "key", "kid", "kill", "kind", "kitchen",
"know", "knowledge", "land", "language", "large", "last", "late", "later", "laugh",
"law", "lawyer", "lay", "lead", "leader", "learn", "least", "leave", "left", "leg",
"legal", "less", "let", "letter", "level", "lie", "life", "light", "like", "likely",
"line", "list", "listen", "little", "live", "local", "long", "look", "lose", "loss",
"lot", "love", "low", "machine", "magazine", "main", "maintain", "major", "majority",
"make", "man", "manage", "management", "manager", "many", "market", "marriage",
"material", "matter", "may", "maybe", "me", "mean", "measure", "media", "medical",
"meet", "meeting", "member", "memory", "mention", "message", "method", "middle",
"might", "military", "million", "mind", "minute", "miss", "mission", "model", "modern",
"moment", "money", "month", "more", "morning", "most", "mother", "mouth", "move",
"movement", "movie", "Mr", "Mrs", "much", "music", "must", "my", "myself", "name",
"nation", "national", "natural", "nature", "near", "nearly", "necessary", "need",
"network", "never", "new", "news", "newspaper", "next", "nice", "night", "no", "none",
"nor", "north", "not", "note", "nothing", "notice", "now", "n't", "number", "occur",
"of", "off", "offer", "office", "officer", "official", "often", "oh", "oil", "ok",
"old", "on", "once", "one", "only", "onto", "open", "operation", "opportunity",
"option", "or", "order", "organization", "other", "others", "our", "out", "outside",
"over", "own", "owner", "page", "pain", "painting", "paper", "parent", "part",
"participant", "particular", "particularly", "partner", "party", "pass", "past",
"patient", "pattern", "pay", "peace", "people", "per", "perform", "performance",
"perhaps", "period", "person", "personal", "phone", "physical", "pick", "picture",
"piece", "place", "plan", "plant", "play", "player", "PM", "point", "police", "policy",
"political", "politics", "poor", "popular", "population", "position", "positive",
"possible", "power", "practice", "prepare", "present", "president", "pressure",
"pretty", "prevent", "price", "private", "probably", "problem", "process", "produce",
"product", "production", "professional", "professor", "program", "project", "property",
"protect", "prove", "provide", "public", "pull", "purpose", "push", "put", "quality",
"question", "quickly", "quite", "race", "radio", "raise", "range", "rate", "rather",
"reach", "read", "ready", "real", "reality", "realize", "really", "reason", "receive",
"recent", "recently", "recognize", "record", "red", "reduce", "reflect", "region",
"relate", "relationship", "religious", "remain", "remember", "remove", "report",
"represent", "Republican", "require", "research", "resource", "respond", "response",
"responsibility", "rest", "result", "return", "reveal", "rich", "right", "rise", "risk",
"road", "rock", "role", "room", "rule", "run", "safe", "same", "save", "say", "scene",
"school", "science", "scientist", "score", "sea", "season", "seat", "second", "section",
"security", "see", "seek", "seem", "sell", "send", "senior", "sense", "series",
"serious", "serve", "service", "set", "seven", "several", "sex", "sexual", "shake",
"share", "she", "shoot", "short", "shot", "should", "shoulder", "show", "side", "sign",
"significant", "similar", "simple", "simply", "since", "sing", "single", "sister",
"sit", "site", "situation", "six", "size", "skill", "skin", "small", "smile", "so",
"social", "society", "soldier", "some", "somebody", "someone", "something", "sometimes",
"son", "song", "soon", "sort", "sound", "source", "south", "southern", "space", "speak",
"special", "specific", "speech", "spend", "sport", "spring", "staff", "stage", "stand",
"standard", "star", "start", "state", "statement", "station", "stay", "step", "still",
"stock", "stop", "store", "story", "strategy", "street", "strong", "structure",
"student", "study", "stuff", "style", "subject", "success", "successful", "such",
"suddenly", "suffer", "suggest", "summer", "support", "sure", "surface", "system",
"table", "take", "talk", "task", "tax", "teach", "teacher", "team", "technology",
"television", "tell", "ten", "tend", "term", "test", "than", "thank", "that", "the",
"their", "them", "themselves", "then", "theory", "there", "these", "they", "thing",
"think", "third", "this", "those", "though", "thought", "thousand", "threat", "three",
"through", "throughout", "throw", "thus", "time", "to", "today", "together", "tonight",
"too", "top", "total", "tough", "toward", "town", "trade", "traditional", "training",
"travel", "treat", "treatment", "tree", "trial", "trip", "trouble", "true", "truth",
"try", "turn", "TV", "two", "type", "under", "understand", "unit", "until", "up",
"upon", "us", "use", "usually", "value", "various", "very", "victim", "view",
"violence", "visit", "voice", "vote", "wait", "walk", "wall", "want", "war", "watch",
"water", "way", "we", "weapon", "wear", "week", "weight", "well", "west", "western",
"what", "whatever", "when", "where", "whether", "which", "while", "white", "who",
"whole", "whom", "whose", "why", "wide", "wife", "will", "win", "wind", "window",
"wish", "with", "within", "without", "woman", "wonder", "word", "work", "worker",
"world", "worry", "would", "write", "writer", "wrong", "yard", "yeah", "year", "yes",
"yet", "you", "young", "your", "yourself")

    val [n : int] n = find_length words_list

     val [p_words : addr]
         @(pf_words, pfgc_words | p_words) =
      array_ptr_alloc<string> n
    val [p_scrambled_words : addr] 
        @(pf_scrambled_words, pfgc_scrambled_words |
          p_scrambled_words) =
      array_ptr_alloc<string> n
    val [p_sorted_words : addr]
        @(pf_sorted_words, pfgc_sorted_words | p_sorted_words) =
      array_ptr_alloc<string> n

    macdef words = !p_words
    macdef scrambled_words = !p_scrambled_words
    macdef sorted_words = !p_sorted_words

    implement
    patience_sort$cmp<string> (x, y) =
      let
        val s = g1ofg0 x
        and t = g1ofg0 y
      in
        if iseqz s then
          (if iseqz t then 0 else ~1)
        else if iseqz t then
          1
        else
          let
            val cs = tolower s[0]
            and ct = tolower t[0]
          in
            if cs < ct then
              ~1
            else if cs = ct then
              0
            else
              1
          end
      end
  in
    array_initize_list<string> (words, sz2i n, words_list);
    scramble_words (n, words, scrambled_words);
    patience_sort<string> (scrambled_words, n, sorted_words);

    let  (* Check that sorted_words has the same contents as words. *)
      var i : [i : nat | i <= n] size_t i
    in
      for (i := i2sz 0; i <> n; i := succ i)
        let
          val (pf0, fpf0 | p0) =
            $UN.ptr0_vtake {array (string, n)} p_words
          and (pf1, fpf1 | p1) =
            $UN.ptr0_vtake {array (string, n)} p_sorted_words
          macdef words = !p0
          macdef sorted_words = !p1
          val s0 : string = words[i]
          and s1 : string = sorted_words[i]

          val () = assertloc (s0 = s1)

          prval () = fpf0 pf0
          prval () = fpf1 pf1
        in
        end
    end;

    array_ptr_free (pf_words, pfgc_words | p_words);
    array_ptr_free (pf_scrambled_words, pfgc_scrambled_words |
                    p_scrambled_words);
    array_ptr_free (pf_sorted_words, pfgc_sorted_words |
                    p_sorted_words)
  end

implement
main0 () =
  begin
    test_stable_sort ()
  end
