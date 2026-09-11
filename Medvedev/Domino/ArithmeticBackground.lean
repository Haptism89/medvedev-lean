import Medvedev.Domino.Periodic
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
A fixed finite background for Jeandel's construction. Rows multiply their
average digit by 2 or divide it by 3. Positive averages cannot follow a finite
cycle, since a positive power of 2 cannot equal a positive power of 3.

The existence proof uses floor differences of rational slopes in [1,6).
This is an explicit arithmetic background, not an assumed aperiodic tileset.
Only a quadrant tiling and absence of torus tilings are needed by the compiler.
-/

namespace Medvedev.Domino.ArithmeticBackground

structure RawTile where
  double : Bool
  south : Fin 6
  north : Fin 6
  west : Fin 6
  east : Fin 6
  deriving DecidableEq, Fintype

def numerator (b : Bool) : ℕ := if b then 2 else 1
def denominator (b : Bool) : ℕ := if b then 1 else 3

def Balanced (t : RawTile) : Prop :=
  denominator t.double * (t.north.val + 1) + t.east.val =
    numerator t.double * (t.south.val + 1) + t.west.val

instance (t : RawTile) : Decidable (Balanced t) := inferInstanceAs (Decidable (_ = _))

abbrev Tile := {t : RawTile // Balanced t}

def system : Wang Tile where
  horizontal t u := t.val.double = u.val.double ∧ t.val.east = u.val.west
  vertical t u := t.val.north = u.val.south

instance : DecidableRel system.horizontal := fun _ _ => inferInstanceAs (Decidable (_ ∧ _))
instance : DecidableRel system.vertical := fun _ _ => inferInstanceAs (Decidable (_ = _))

/-- The next slope stays in the same bounded positive interval. -/
def nextSlope (x : ℚ) : ℚ := if x < 3 then 2 * x else x / 3

theorem nextSlope_bounds {x : ℚ} (hlo : 1 ≤ x) (hhi : x < 6) :
    1 ≤ nextSlope x ∧ nextSlope x < 6 := by
  unfold nextSlope
  split_ifs with h <;> constructor <;> linarith

def slope : ℕ → ℚ
  | 0 => 1
  | n + 1 => nextSlope (slope n)

theorem slope_bounds (n : ℕ) : 1 ≤ slope n ∧ slope n < 6 := by
  induction n with
  | zero => norm_num [slope]
  | succ n ih => exact nextSlope_bounds ih.1 ih.2

def floorDigit (x : ℚ) (i : ℕ) : ℤ := ⌊((i : ℚ) + 1) * x⌋ - ⌊(i : ℚ) * x⌋

theorem floorDigit_bounds {x : ℚ} (hlo : 1 ≤ x) (hhi : x < 6) (i : ℕ) :
    1 ≤ floorDigit x i ∧ floorDigit x i ≤ 6 := by
  have hl := Int.floor_le ((i : ℚ) * x)
  have hu := Int.lt_floor_add_one ((i : ℚ) * x)
  have hnext := Int.floor_le (((i : ℚ) + 1) * x)
  have hone : ⌊(i : ℚ) * x⌋ + 1 ≤ ⌊((i : ℚ) + 1) * x⌋ := by
    apply Int.le_floor.mpr
    push_cast
    nlinarith
  have hsix : (⌊((i : ℚ) + 1) * x⌋ : ℚ) < (⌊(i : ℚ) * x⌋ : ℚ) + 7 := by
    nlinarith
  have hsix' : ⌊((i : ℚ) + 1) * x⌋ < ⌊(i : ℚ) * x⌋ + 7 := by exact_mod_cast hsix
  dsimp [floorDigit]
  omega

def digit (x : ℚ) (hlo : 1 ≤ x) (hhi : x < 6) (i : ℕ) : Fin 6 :=
  ⟨(floorDigit x i - 1).toNat, by
    obtain ⟨hl, hu⟩ := floorDigit_bounds hlo hhi i
    omega⟩

theorem digit_value (x : ℚ) (hlo : 1 ≤ x) (hhi : x < 6) (i : ℕ) :
    ((digit x hlo hhi i).val : ℤ) + 1 = floorDigit x i := by
  have hl := (floorDigit_bounds hlo hhi i).1
  simp only [digit]
  omega

def mode (x : ℚ) : Bool := decide (x < 3)

def carry (x : ℚ) (i : ℕ) : ℤ :=
  (numerator (mode x) : ℤ) * ⌊(i : ℚ) * x⌋ -
    (denominator (mode x) : ℤ) * ⌊(i : ℚ) * nextSlope x⌋ + 2

theorem carry_bounds (x : ℚ) (i : ℕ) : 0 ≤ carry x i ∧ carry x i < 6 := by
  have ha := Int.floor_le ((i : ℚ) * x)
  have ha' := Int.lt_floor_add_one ((i : ℚ) * x)
  have hb := Int.floor_le ((i : ℚ) * nextSlope x)
  have hb' := Int.lt_floor_add_one ((i : ℚ) * nextSlope x)
  by_cases h : x < 3
  · simp only [nextSlope, if_pos h] at hb hb'
    have hlo : (-2 : ℚ) < 2 * (⌊(i : ℚ) * x⌋ : ℚ) - ⌊(i : ℚ) * (2 * x)⌋ := by
      nlinarith
    have hhi : 2 * (⌊(i : ℚ) * x⌋ : ℚ) - ⌊(i : ℚ) * (2 * x)⌋ < (1 : ℚ) := by
      nlinarith
    have hlo' : (-2 : ℤ) < 2 * ⌊(i : ℚ) * x⌋ - ⌊(i : ℚ) * (2 * x)⌋ := by exact_mod_cast hlo
    have hhi' : 2 * ⌊(i : ℚ) * x⌋ - ⌊(i : ℚ) * (2 * x)⌋ < (1 : ℤ) := by exact_mod_cast hhi
    simp [carry, mode, numerator, denominator, nextSlope, h]
    omega
  · simp only [nextSlope, if_neg h] at hb hb'
    have hlo : (-1 : ℚ) < (⌊(i : ℚ) * x⌋ : ℚ) - 3 * ⌊(i : ℚ) * (x / 3)⌋ := by
      nlinarith
    have hhi : (⌊(i : ℚ) * x⌋ : ℚ) - 3 * ⌊(i : ℚ) * (x / 3)⌋ < (3 : ℚ) := by
      nlinarith
    have hlo' : (-1 : ℤ) < ⌊(i : ℚ) * x⌋ - 3 * ⌊(i : ℚ) * (x / 3)⌋ := by exact_mod_cast hlo
    have hhi' : ⌊(i : ℚ) * x⌋ - 3 * ⌊(i : ℚ) * (x / 3)⌋ < (3 : ℤ) := by exact_mod_cast hhi
    simp [carry, mode, numerator, denominator, nextSlope, h]
    omega

def carryColor (x : ℚ) (i : ℕ) : Fin 6 :=
  ⟨(carry x i).toNat, by have h := carry_bounds x i; omega⟩

theorem carryColor_value (x : ℚ) (i : ℕ) : ((carryColor x i).val : ℤ) = carry x i := by
  have h := (carry_bounds x i).1
  simp [carryColor, Int.toNat_of_nonneg h]

def rawAt (i j : ℕ) : RawTile where
  double := mode (slope j)
  south := digit (slope j) (slope_bounds j).1 (slope_bounds j).2 i
  north := digit (slope (j + 1)) (slope_bounds (j + 1)).1 (slope_bounds (j + 1)).2 i
  west := carryColor (slope j) i
  east := carryColor (slope j) (i + 1)

theorem rawAt_balanced (i j : ℕ) : Balanced (rawAt i j) := by
  unfold Balanced rawAt
  apply Int.natCast_inj.mp
  push_cast
  rw [digit_value, digit_value, carryColor_value, carryColor_value]
  simp only [carry, slope, floorDigit, Nat.cast_add, Nat.cast_one]
  ring

/-- An actual infinite tiling, with every tile in the explicitly finite set. -/
def quarter : QuarterTiling system where
  tile i j := ⟨rawAt i j, rawAt_balanced i j⟩
  horizontal _ _ := ⟨rfl, rfl⟩
  vertical _ _ := rfl

end Medvedev.Domino.ArithmeticBackground
