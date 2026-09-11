import Medvedev.Domino.Plane
import Mathlib.Data.Fintype.Prod

namespace Medvedev.Domino

/-- A local neighbourhood converts arbitrary directed compatibility relations
to literal edge-colour matching. Every component is an original tile label. -/
structure ColoredTile {T : Type} (D : Wang T) where
  center : T
  west : T
  east : T
  south : T
  north : T
  west_ok : D.horizontal west center
  east_ok : D.horizontal center east
  south_ok : D.vertical south center
  north_ok : D.vertical center north

instance {T : Type} [Finite T] (D : Wang T) : Finite (ColoredTile D) := by
  classical
  letI := Fintype.ofFinite T
  let f : ColoredTile D → T × T × T × T × T :=
    fun t => (t.center, t.west, t.east, t.south, t.north)
  apply Finite.of_injective f
  intro a b h
  cases a
  cases b
  simp only [f, Prod.mk.injEq] at h
  rcases h with ⟨rfl, rfl, rfl, rfl, rfl⟩
  rfl

/-- East/west colours are pairs of horizontally adjacent labels; north/south
colours are pairs of vertically adjacent labels. The colour alphabet is T×T. -/
def coloredSystem {T : Type} (D : Wang T) : Wang (ColoredTile D) where
  horizontal t u := (t.center, t.east) = (u.west, u.center)
  vertical t u := (t.center, t.north) = (u.south, u.center)

theorem colored_torus_iff {T : Type} (D : Wang T) (m n : ℕ) :
    Nonempty (Medvedev.TorusTiling (coloredSystem D) m n) ↔
      Nonempty (Medvedev.TorusTiling D m n) := by
  constructor
  · rintro ⟨c⟩
    refine ⟨⟨fun i j => (c.tile i j).center, ?_, ?_⟩⟩
    · intro i j
      have h := congrArg Prod.snd (c.horizontal i j)
      dsimp at h
      simpa only [h] using (c.tile i j).east_ok
    · intro i j
      have h := congrArg Prod.snd (c.vertical i j)
      dsimp at h
      simpa only [h] using (c.tile i j).north_ok
  · rintro ⟨c⟩
    let t : Fin (m + 1) → Fin (n + 1) → ColoredTile D := fun i j => {
      center := c.tile i j
      west := c.tile ((finRotate (m + 1)).symm i) j
      east := c.tile (finRotate (m + 1) i) j
      south := c.tile i ((finRotate (n + 1)).symm j)
      north := c.tile i (finRotate (n + 1) j)
      west_ok := by simpa using c.horizontal ((finRotate (m + 1)).symm i) j
      east_ok := c.horizontal i j
      south_ok := by simpa using c.vertical i ((finRotate (n + 1)).symm j)
      north_ok := c.vertical i j
    }
    refine ⟨⟨t, ?_, ?_⟩⟩
    · intro i j
      simp [coloredSystem, t]
    · intro i j
      simp [coloredSystem, t]

theorem tilesTorus_colored_iff {T : Type} (D : Wang T) :
    TilesTorus (coloredSystem D) ↔ TilesTorus D := by
  simp only [TilesTorus, colored_torus_iff]

end Medvedev.Domino
