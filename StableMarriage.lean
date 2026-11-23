
import Mathlib

variable {n : ℕ}

-- ============================================================
-- PART 1: BASIC DEFINITIONS
-- ============================================================

-- n men and n women, represented by Fin n
-- Fin n contains the numbers 0, 1, ..., n-1

-- mp m gives man m's preference list, ranked best to worst
-- wp w gives woman w's preference list, ranked best to worst
-- both have type Fin n → List (Fin n)

-- a valid ranking contains every possible partner exactly once
-- the list has n entries and contains every possible partner
-- since there are only n possible partners, there are no duplicates
def ValidRanking (ranking : List (Fin n)) : Prop :=
  ranking.length = n ∧
  (∀ a : Fin n, a ∈ ranking)

-- matching is a bijection from men to women
abbrev Matching (n : ℕ) := Fin n ≃ Fin n

-- a matching is stable if no man and woman prefer each other
-- over their current partners
-- idxOf gives the position of a person in a ranking
-- smaller position means higher preference
def Stable
    (mp : Fin n → List (Fin n))
    (wp : Fin n → List (Fin n))
    (μ : Matching n) : Prop :=
  ¬ ∃ m w,
    (mp m).idxOf w < (mp m).idxOf (μ m) ∧
    (wp w).idxOf m < (wp w).idxOf (μ.symm w)

-- ============================================================
-- PART 2: PROPERTIES OF PREFERENCE LISTS
-- ============================================================

-- thm 1: a person cannot prefer someone over themselves
theorem prefers_irreflexive
    (ranking : List (Fin n))
    (a : Fin n) :
    ¬ ranking.idxOf a < ranking.idxOf a := by
  omega

-- thm 2: if a is preferred over b,
-- then b cannot also be preferred over a
theorem prefers_asymmetric
    (ranking : List (Fin n))
    (a b : Fin n)
    (h : ranking.idxOf a < ranking.idxOf b) :
    ¬ ranking.idxOf b < ranking.idxOf a := by
  omega

-- thm 3: preferences are transitive
-- if a is preferred over b and b over c,
-- then a is preferred over c
theorem prefers_transitive
    (ranking : List (Fin n))
    (a b c : Fin n)
    (hab : ranking.idxOf a < ranking.idxOf b)
    (hbc : ranking.idxOf b < ranking.idxOf c) :
    ranking.idxOf a < ranking.idxOf c := by
  omega

-- thm 4: a man cannot form a blocking pair
-- with his current partner
theorem current_partner_not_blocking_man
    (mp : Fin n → List (Fin n))
    (wp : Fin n → List (Fin n))
    (μ : Matching n)
    (m : Fin n) :
    ¬ ((mp m).idxOf (μ m) < (mp m).idxOf (μ m) ∧
       (wp (μ m)).idxOf m <
         (wp (μ m)).idxOf (μ.symm (μ m))) := by
  intro h
  exact prefers_irreflexive (mp m) (μ m) h.1

-- thm 5: a woman cannot form a blocking pair
-- with her current partner
theorem current_partner_not_blocking_woman
    (mp : Fin n → List (Fin n))
    (wp : Fin n → List (Fin n))
    (μ : Matching n)
    (w : Fin n) :
    ¬ ((mp (μ.symm w)).idxOf w <
         (mp (μ.symm w)).idxOf (μ (μ.symm w)) ∧
       (wp w).idxOf (μ.symm w) <
         (wp w).idxOf (μ.symm w)) := by
  intro h
  exact prefers_irreflexive (wp w) (μ.symm w) h.2

-- ============================================================
-- PART 3: GALE-SHAPLEY DATA STRUCTURES
-- ============================================================

-- partial matching keeps track of current partners
-- μ w = some m means woman w is currently matched to man m
-- μ w = none means woman w is currently unmatched
abbrev PartialMatching (n : ℕ) :=
  Fin n → Option (Fin n)

-- proposal history keeps track of who each man proposed to
-- history m is the list of women man m has already proposed to
abbrev ProposalHistory (n : ℕ) :=
  Fin n → List (Fin n)

-- ============================================================
-- PART 4: GALE-SHAPLEY HELPER FUNCTIONS
-- ============================================================

-- find the next woman a man should propose to
-- preferences are ranked best to worst
-- find the first woman he has not already proposed to
def nextProposal
    (mp : Fin n → List (Fin n))
    (m : Fin n)
    (proposed : List (Fin n)) : Option (Fin n) :=
  (mp m).find? (fun w => w ∉ proposed)

-- determine whether a woman accepts a proposal
-- if unmatched, she accepts the new man
-- if matched, she keeps whichever man she prefers
def acceptProposal
    (wp : Fin n → List (Fin n))
    (w : Fin n)
    (current : Option (Fin n))
    (newMan : Fin n) : Option (Fin n) :=
  match current with
  | none => some newMan
  | some oldMan =>
      if (wp w).idxOf newMan < (wp w).idxOf oldMan then
        some newMan
      else
        some oldMan

-- update the temporary matching after a woman receives a proposal
-- only the woman receiving the proposal can change partners
def updateMatching
    (wp : Fin n → List (Fin n))
    (μ : PartialMatching n)
    (w : Fin n)
    (m : Fin n) : PartialMatching n :=
  fun w₂ =>
    if w₂ = w then
      acceptProposal wp w (μ w) m
    else
      μ w₂

-- check whether a man is currently matched
-- a man is matched if some woman has him as her partner
def isMatched
    (μ : PartialMatching n)
    (m : Fin n) : Bool :=
  (List.finRange n).any (fun w => μ w == some m)

-- find the first unmatched man
-- includes men who became unmatched after being replaced
def findUnmatched
    (μ : PartialMatching n) : Option (Fin n) :=
  (List.finRange n).find? (fun m => !isMatched μ m)

-- record a new proposal in a man's history
-- other men's histories remain unchanged
def addProposal
    (history : ProposalHistory n)
    (m : Fin n)
    (w : Fin n) : ProposalHistory n :=
  fun m₂ =>
    if m₂ = m then
      w :: history m
    else
      history m₂

-- ============================================================
-- PART 5: MAIN GALE-SHAPLEY ALGORITHM
-- ============================================================

-- initially, every woman is unmatched
def emptyMatching : PartialMatching n :=
  fun _ => none

-- initially, no man has proposed to anyone
def emptyHistory : ProposalHistory n :=
  fun _ => []

-- Gale-Shapley algorithm
-- each unmatched man proposes to women in preference order
-- women keep their favorite proposal received so far
-- fuel ensures the algorithm terminates
-- returns both the partial matching and proposal history
def galeShapley
    (mp : Fin n → List (Fin n))
    (wp : Fin n → List (Fin n)) :
    Nat → PartialMatching n →
    ProposalHistory n →
    PartialMatching n × ProposalHistory n
  | 0, μ, history => (μ, history)
  | fuel + 1, μ, history =>
      match findUnmatched μ with
      | none => (μ, history)
      | some m =>
          match nextProposal mp m (history m) with
          | none => (μ, history)
          | some w =>
              -- record the proposal
              let newHistory := addProposal history m w
              -- woman decides whether to accept the proposal
              let newMatching := updateMatching wp μ w m
              -- continue with updated matching and history
              galeShapley mp wp fuel newMatching newHistory

-- run Gale-Shapley with at most n² proposals
-- return the final matching and the complete proposal history
def runGaleShapley
    (mp : Fin n → List (Fin n))
    (wp : Fin n → List (Fin n)) :
    PartialMatching n × ProposalHistory n :=
  galeShapley mp wp (n * n) emptyMatching emptyHistory
