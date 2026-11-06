import StableMarriage.Basic
import MathLib

variable {M W : Type}

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

-- defining valid preferences

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

-- properties

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
