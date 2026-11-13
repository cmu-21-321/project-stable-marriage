
import StableMarriage.Basic
import Mathlib

variable {M W : Type}

-- ============================================================
-- PART 1: BASIC DEFINITIONS
-- ============================================================

-- man's pref between two women
def MenPref (M W : Type) := M → W → W → Prop

-- women's pref between two men
def WomenPref (M W : Type) := W → M → M → Prop

-- matching is a bijection from men to women
abbrev Matching (M W : Type) := M ≃ W

-- a blocking pair occurs either if a man prefers another woman
-- over his current matching or a woman prefers another man over
-- her current matching
def BlockingPair
    (mp : MenPref M W)
    (wp : WomenPref M W)
    (μ : Matching M W)
    (m : M) (w : W) : Prop :=
  mp m w (μ m) ∧
  wp w m (μ.symm w)

-- if there doesn't exist a blocking pair for some w and m,
-- marriage is stable
def Stable
    (mp : MenPref M W)
    (wp : WomenPref M W)
    (μ : Matching M W) : Prop :=
  ¬ ∃ m w, BlockingPair mp wp μ m w


-- ============================================================
-- PART 2: DEFINING VALID PREFERENCES
-- ============================================================

-- man cannot prefer a woman over herself
def MenIrreflexive (mp : MenPref M W) : Prop :=
  ∀ m w, ¬ mp m w w
  -- for every man and woman, it is not true that a man
  -- prefers woman w over herself

-- woman cannot prefer a man over himself
def WomenIrreflexive (wp : WomenPref M W) : Prop :=
  ∀ w m, ¬ wp w m m

-- men's preferences are transitive
def MenTransitive (mp : MenPref M W) : Prop :=
  ∀ m w₁ w₂ w₃,
    mp m w₁ w₂ →
    mp m w₂ w₃ →
    mp m w₁ w₃
    -- if a man prefers woman 1 over woman 2, and prefers
    -- woman 2 over woman 3, he must prefer woman 1 over woman 3

-- women's preferences are transitive
def WomenTransitive (wp : WomenPref M W) : Prop :=
  ∀ w m₁ m₂ m₃,
    wp w m₁ m₂ →
    wp w m₂ m₃ →
    wp w m₁ m₃

-- completeness
-- man can compare any two different women
def MenComplete (mp : MenPref M W) : Prop :=
  ∀ m w₁ w₂,
    w₁ ≠ w₂ →
    mp m w₁ w₂ ∨ mp m w₂ w₁
    -- if both women are different, there must be a pref

-- woman can compare any two different men
def WomenComplete (wp : WomenPref M W) : Prop :=
  ∀ w m₁ m₂,
    m₁ ≠ m₂ →
    wp w m₁ m₂ ∨ wp w m₂ m₁


-- ============================================================
-- PART 3: PROPERTIES OF VALID PREFERENCES
-- ============================================================

-- thm 1: a person cannot form a blocking pair with their current partner
theorem current_partner_not_blocking_man
    (mp : MenPref M W)
    (wp : WomenPref M W)
    (μ : Matching M W)
    (hmp : MenIrreflexive mp)
    (m : M) :
    ¬ BlockingPair mp wp μ m (μ m) := by
  intro h
  -- assumes man and his current partner form a blocking pair
  unfold BlockingPair at h
  obtain ⟨hm, hw⟩ := h
  exact hmp m (μ m) hm
  -- uses contradiction that the man cannot prefer his current partner over herself

theorem current_partner_not_blocking_woman
    (mp : MenPref M W)
    (wp : WomenPref M W)
    (μ : Matching M W)
    (hwp : WomenIrreflexive wp)
    (w : W) :
    ¬ BlockingPair mp wp μ (μ.symm w) w := by
  intro h
  -- assume woman and her current partner form a blocking pair
  unfold BlockingPair at h
  obtain ⟨hm, hw⟩ := h
  -- woman cannot prefer her current partner over himself
  exact hwp w (μ.symm w) hw

-- thm 2: if a person prefers person 1 over person 2, they can't also
-- prefer person 2 over person 1

theorem men_asymmetric
    (mp : MenPref M W)
    (hirr : MenIrreflexive mp)
    (htrans : MenTransitive mp)
    (m : M) (w₁ w₂ : W)
    (h : mp m w₁ w₂) :
    ¬ mp m w₂ w₁ := by
    -- if h where m prefers w1 over w2, it can't be true that
    -- the opposite holds
  intro hreverse
  -- assume man also prefers woman 2 over woman 1
  -- prove false
  have hself : mp m w₁ w₁ := htrans m w₁ w₂ w₁ h hreverse
  -- transitivity would mean he prefers woman 1 over herself
  exact hirr m w₁ hself
  -- irreflexive gives false

theorem women_asymmetric
    (wp : WomenPref M W)
    (hirr : WomenIrreflexive wp)
    (htrans : WomenTransitive wp)
    (w : W) (m₁ m₂ : M)
    (h : wp w m₁ m₂) :
    ¬ wp w m₂ m₁ := by
  -- if woman w prefers m1 over m2, it can't be true that
  -- the opposite holds
  intro hreverse
  -- assume woman also prefers man 2 over man 1
  -- prove false
  have hself : wp w m₁ m₁ := htrans w m₁ m₂ m₁ h hreverse
  -- transitivity would mean she prefers man 1 over himself
  exact hirr w m₁ hself
  -- irreflexivity gives false

-- thm 3: uniquness of pref direction

theorem men_unique_preference
    (mp : MenPref M W)
    (hirr : MenIrreflexive mp)
    (htrans : MenTransitive mp)
    (hcomp : MenComplete mp)
    (m : M) (w₁ w₂ : W)
    (hne : w₁ ≠ w₂) :
    (mp m w₁ w₂ ∧ ¬ mp m w₂ w₁) ∨
    (mp m w₂ w₁ ∧ ¬ mp m w₁ w₂) := by
    -- one of the two possibilities must hold
  rcases hcomp m w₁ w₂ hne with h12 | h21
  -- case on w1>w2 and w2>w1
  · left
    -- prove mp m w₁ w₂ ∧ ¬ mp m w₂ w
    constructor
    -- h12 shows that w1>w2
    · exact h12
    -- asymmetric shows that other side not true
    · exact men_asymmetric mp hirr htrans m w₁ w₂ h12
  · right
    constructor
    · exact h21
    · exact men_asymmetric mp hirr htrans m w₂ w₁ h21

theorem women_unique_preference
    (wp : WomenPref M W)
    (hirr : WomenIrreflexive wp)
    (htrans : WomenTransitive wp)
    (hcomp : WomenComplete wp)
    (w : W) (m₁ m₂ : M)
    (hne : m₁ ≠ m₂) :
    (wp w m₁ m₂ ∧ ¬ wp w m₂ m₁) ∨
    (wp w m₂ m₁ ∧ ¬ wp w m₁ m₂) := by
    -- one of the two possibilities must hold
  rcases hcomp w m₁ m₂ hne with h12 | h21
  -- case on m1>m2 and m2>m1
  · left
    -- prove wp w m₁ m₂ ∧ ¬ wp w m₂ m₁
    constructor
    -- h12 shows that woman prefers m1 over m2
    · exact h12
    -- asymmetry shows that the opposite preference cannot hold
    · exact women_asymmetric wp hirr htrans w m₁ m₂ h12
  · right
    -- prove wp w m₂ m₁ ∧ ¬ wp w m₁ m₂
    constructor
    -- h21 shows that woman prefers m2 over m1
    · exact h21
    -- asymmetry shows that the opposite preference cannot hold
    · exact women_asymmetric wp hirr htrans w m₂ m₁ h21


-- ============================================================
-- PART 4: GALE-SHAPLEY DATA STRUCTURES
-- ============================================================

-- partial matching keeps track of who's dating whom
-- while the algorithm runs (some people won't have partners yet)
def PartialMatching (M W : Type) :=
  W → Option M
-- some m — the woman is currently matched with man m
-- none — the woman doesn't have a partner yet

-- ProposalHistory: keeps track of which women
-- each man has already proposed to
def ProposalHistory (M W : Type) :=
  M → List W


-- ============================================================
-- PART 5: GALE-SHAPLEY HELPER FUNCTIONS
-- ============================================================

-- bestWoman: uses menPref to find man's favorite
-- woman from list
def bestWoman
    (mp : MenPref M W)
    (m : M)
    [DecidableRel (mp m)] :
    List W → Option W
  | [] => none
  -- if list empty then there is no woman to choose
  | w :: ws =>
      -- recursively find the best woman in the remaining list
      match bestWoman mp m ws with
      -- if no woman remains, w is the best choice
      | none => some w
      -- if the remaining list has a best woman w₂,
      -- compare w with w₂
      | some w₂ =>
          if mp m w w₂ then some w
          else some w₂

-- remainingWomen: remove women who already received a proposal
-- so no one is proposed to twice

def remainingWomen [BEq W] :
    List W → List W → List W
    -- if there are no women left, return an empty list
  | [], _ => []
  -- take the first woman w and the remaining women ws
  -- proposed is the list of women already proposed to
  | w :: ws, proposed =>
      -- check whether w is in the proposed list
      if proposed.contains w then
        -- if w already received a proposal, skip her
        remainingWomen ws proposed
      else
        -- otherwise, keep w and check the rest of the list
        w :: remainingWomen ws proposed

-- nextProposal: finds next woman a man should propose to,
-- skipping anyone who already rejected him
def nextProposal
    [BEq W]
    (mp : MenPref M W)
    (m : M)
    [DecidableRel (mp m)]
    (women : List W)
    (proposed : List W) : Option W :=
  -- first remove women who already received a proposal
  -- then find the man's favorite among the remaining women
  bestWoman mp m (remainingWomen women proposed)

-- acceptProposal: determine whether a woman accepts a proposal
-- uses our existing WomenPref to compare men

def acceptProposal
    (wp : WomenPref M W)
    (w : W)
    [DecidableRel (wp w)]
    (current : Option M)
    (newMan : M) : Option M :=
  -- check whether the woman already has a partner
  match current with
  -- if she is unmatched, she accepts the new man
  | none => some newMan
  -- if she is already matched with oldMan,
  -- compare her current partner with the new man
  | some oldMan =>
      -- if she prefers newMan over oldMan,
      -- she leaves oldMan and accepts newMan
      if wp w newMan oldMan then
        some newMan
      -- otherwise, she rejects newMan
      -- and keeps her current partner
      else
        some oldMan

-- updateMatching: updates the temporary matching
-- after a woman receives a proposal
def updateMatching
    [BEq W]
    (wp : WomenPref M W)
    [∀ w, DecidableRel (wp w)]
    (μ : PartialMatching M W)
    (w : W)
    (m : M) : PartialMatching M W :=
  -- return a new matching function
  fun w₂ =>
    -- check if w₂ is the woman receiving the proposal
    if w₂ == w then
      -- use acceptProposal to determine her new partner
      acceptProposal wp w (μ w) m
    else
      -- all other women keep their current partners
      μ w₂

-- find whether a man is currently matched
-- check if any woman has this man as her partner
def isMatched [BEq M]
    (μ : PartialMatching M W)
    (m : M) : List W → Bool
  | [] => false
    -- if no women left, then the man is not matched
  | w :: ws =>
  -- if women left
      -- if the women is macthed w the man return true
      if μ w == some m then true
      -- else check remaining women
      else isMatched μ m ws

-- find the first unmatched man
-- also finds men who became unmatched after being replaced
def findUnmatched [BEq M]
    (μ : PartialMatching M W)
    (women : List W) : List M → Option M
    -- if no men left to check, no unmatched man in list
  | [] => none
  | m :: ms =>
  -- check if m matched to any woman
  -- if m alresady macthed, skip him
      if isMatched μ m women then
        findUnmatched μ women ms
      else
      -- else return him
        some m

-- addProposal: records a new proposal in a man's history
def addProposal [BEq M]
    (history : ProposalHistory M W)
    (m : M)
    (w : W) : ProposalHistory M W :=
  -- create an updated proposal history
  fun m₂ =>
    -- check if m₂ is the man who just proposed
    if m₂ == m then
      -- add woman w to his list of previous proposals
      w :: history m
    else
      -- all other men keep their previous proposal histories
      history m₂


-- ============================================================
-- PART 6: MAIN GALE-SHAPLEY ALGORITHM
-- ============================================================

-- initially, every woman is unmatched
def emptyMatching : PartialMatching M W :=
  fun _ => none

-- initially, no man has made any proposals
def emptyHistory : ProposalHistory M W :=
  fun _ => []

-- start Gale-Shapley
-- at most n² proposals for n men and n women
def galeShapley
    [BEq M] [BEq W]
    (mp : MenPref M W)
    (wp : WomenPref M W)
    [∀ m, DecidableRel (mp m)]
    [∀ w, DecidableRel (wp w)]
    (men : List M)
    (women : List W) :
    Nat → PartialMatching M W →
    ProposalHistory M W → PartialMatching M W
  -- base case: no steps remain
  | 0, μ, _ => μ
  -- recursive case: we have at least one step remaining
  | fuel + 1, μ, history =>
      -- find the first unmatched man
      match findUnmatched μ women men with
      -- if all men are matched, return the matching
      | none => μ
      | some m =>
          -- find his favorite woman he hasn't proposed to
          match nextProposal mp m women (history m) with
          -- if he has no women left to propose to,
          -- return the current matching
          | none => μ
          | some w =>
              -- record that m proposed to w
              let newHistory := addProposal history m w
              -- update the matching based on the woman's preference
              let newMatching := updateMatching wp μ w m
              -- repeat with the updated matching and history
              galeShapley mp wp men women
                fuel newMatching newHistory

-- runGaleShapley: starts the algorithm
-- each man can propose to each woman at most once
def runGaleShapley
    [BEq M] [BEq W]
    (mp : MenPref M W)
    (wp : WomenPref M W)
    [∀ m, DecidableRel (mp m)]
    [∀ w, DecidableRel (wp w)]
    (men : List M)
    (women : List W) : PartialMatching M W :=
  -- start with everyone unmatched and no proposals
    galeShapley mp wp men women
    (men.length * women.length) emptyMatching emptyHistory
