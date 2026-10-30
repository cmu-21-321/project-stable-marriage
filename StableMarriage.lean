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
theorem current_partner_not_blocking
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
