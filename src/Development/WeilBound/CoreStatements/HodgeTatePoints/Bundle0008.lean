import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0001
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0002
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0022
import ReciprocityTheory.DualLattices.Bundle0005
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0003
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0004
import ReciprocityTheory.DualLattices.UpSmith
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0001
import ReciprocityTheory.DualLattices.Bundle0016

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.HtatHt
section
noncomputable section

namespace PositivityTheory.HtPt.Htat

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT

theorem valAt_comp_top {B : Type} [CommRing B] {X Y : Scheme.{0}} (x : Spec (CommRingCat.of B) ⟶ X) (f : X ⟶ Y)
    (s : Γ(Y, ⊤)) : valAt (x ≫ f) ⊤ le_top s = valAt x ⊤ le_top (f.appTop.hom s) := by
  unfold valAt
  congr 1

theorem tors_ext {R : Type} [CommRing R] [IsDomain R] {T : Type} [CommGroup T] {Γ : QFGroup R T} {S : Scheme.{0}}
    {G : Over S} [GrpObj G] {x : Spec (CommRingCat.of R) ⟶ S} {N : ℕ} {i : Γ.G.left ⟶ G.left}
    (h : Γ.IsTorsionAlong G x N i) {Y : Scheme.{0}} {v v' : Y ⟶ Γ.G.left} (h1 : v ≫ Γ.G.hom = v' ≫ Γ.G.hom)
    (h2 : v ≫ i = v' ≫ i) : v = v' :=
  congrArg (·.left) (h.inj (Over.mk (v ≫ Γ.G.hom)) (Over.homMk v rfl) (Over.homMk v' h1.symm) h2)

theorem ht_add : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (x : Spec (CommRingCat.of R) ⟶ S) (N : ℕ) (i : Γ.G.left ⟶ G.left), Γ.IsTorsionAlong G x N i → ∀ (L : Type) [AddCommGroup L] [Module R L] (M : LieModel G x L) (χ χ' : T →* Rˣ) (w w' : Module.Dual R L), Γ.IsHT i M N χ w → Γ.IsHT i M N χ' w' → Γ.IsHT i M N (χ * χ') (w + w') := by
  intro R _ _ T _ _ Γ S G _ _ x N i h L _ _ M χ χ' w w' ⟨s, hs, hv⟩ ⟨s', hs', hv'⟩
  have hm : ∀ {B : Type} [CommRing B] (y : Spec (CommRingCat.of B) ⟶ Γ.G.left),
      valAt y ⊤ le_top (s * s') = valAt y ⊤ le_top s * valAt y ⊤ le_top s' := fun y => by simp [valAt]
  refine ⟨s * s', fun t => ?_, fun e => ?_⟩
  · rw [hm, hs t, hs' t, ← map_mul]; rfl
  · obtain ⟨v, h1, h2, h3⟩ := hv e
    obtain ⟨v', h1', h2', h3'⟩ := hv' e
    obtain rfl : v = v' := tors_ext h (h1.trans h1'.symm) (h2.trans h2'.symm)
    refine ⟨v, h1, h2, ?_⟩
    rw [hm, h3, h3']
    ext <;> simp [add_comm]

theorem ht_olin : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (x : Spec (CommRingCat.of R) ⟶ S) (N : ℕ) (i : Γ.G.left ⟶ G.left), Γ.IsTorsionAlong G x N i → ∀ (L : Type) [AddCommGroup L] [Module R L] (M : LieModel G x L) (a : G ⟶ G) [IsMonHom a] (α : T →* T) (A : L →ₗ[R] L), (∀ t, (Γ.pt (α t)).left ≫ i = (Γ.pt t).left ≫ i ≫ a.left) → M.IsDiffOf a A → ∀ (χ : T →* Rˣ) (w : Module.Dual R L), Γ.IsHT i M N χ w → Γ.IsHT i M N (χ.comp α) (w ∘ₗ A) := by
  intro R _ _ T _ _ Γ S G _ _ x N i h L _ _ M a _ α A hα hA χ w ⟨s, hs, hv⟩
  let g : Over.mk (Γ.G.hom ≫ x) ⟶ G := Over.homMk i h.isOver
  have hg : g ^ N = 1 := (h.kernel Γ.G g).2 ⟨𝟙 _, Category.id_comp _⟩
  have hga : (g ≫ a) ^ N = 1 := by
    have : ∀ n : ℕ, (g ≫ a) ^ n = (g ^ n) ≫ a := fun n => by
      induction n with
      | zero => simp [MonObj.one_comp]
      | succ n ih => rw [pow_succ, pow_succ, ih, MonObj.mul_comp]
    rw [this, hg, MonObj.one_comp]
  obtain ⟨a', ha'⟩ := (h.kernel Γ.G (g ≫ a)).1 hga
  replace ha' : a'.left ≫ i = i ≫ a.left := ha'
  refine ⟨a'.left.appTop.hom s, fun t => ?_, fun e => ?_⟩
  · have : (Γ.pt t).left ≫ a'.left = (Γ.pt (α t)).left :=
      tors_ext h (by rw [Category.assoc, Over.w, Over.w, Over.w]) (by rw [Category.assoc, ha', hα])
    rw [← valAt_comp_top, this]
    exact hs (α t)
  · obtain ⟨v, ⟨h1, h2⟩, -⟩ := GlobalTheory.T.existsUnique_tangent_dual_number R T Γ S G x N i h L M e
    obtain ⟨v', h1', h2', h3'⟩ := hv (A e)
    have : v ≫ a'.left = v' := tors_ext h (by rw [Category.assoc, Over.w, h1, h1']) (by
      rw [Category.assoc, ha', ← Category.assoc, h2, h2', hA e, Over.comp_left, Category.assoc])
    exact ⟨v, h1, h2, by rw [← valAt_comp_top, this, h3']; rfl⟩

end PositivityTheory.HtPt.Htat
end
end

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.PowCongr
section
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

namespace PositivityTheory.HtPt.Rd

theorem powadd : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] (v : Valuation C NNReal) (x y z : C), v x ≤ 1 → v y ≤ 1 → v (z - x - y) ≤ v (p : C) → v (z ^ p - x ^ p - y ^ p) ≤ v (p : C) := by
  intro p hp C _ v x y z hx hy h
  have hp1 : v (p : C) ≤ 1 := by
    exact natCast_mem v.integer p
  have hz : v z ≤ 1 := by
    have e : z = (z - x - y) + x + y := by ring
    rw [e]
    exact v.map_add_le (v.map_add_le (h.trans hp1) hx) hy
  let X : v.integer := ⟨x, hx⟩
  let Y : v.integer := ⟨y, hy⟩
  let Z : v.integer := ⟨z, hz⟩
  obtain ⟨r, hr⟩ := exists_add_pow_prime_eq hp.out X Y
  obtain ⟨s, hs⟩ := sub_dvd_pow_sub_pow Z (X + Y) p
  have hr' := congrArg v.integer.subtype hr
  have hs' := congrArg v.integer.subtype hs
  simp only [map_add, map_mul, map_pow, map_sub, map_natCast, Subring.subtype_apply, X, Y, Z]
    at hr' hs'
  have e : z ^ p - x ^ p - y ^ p = (z - x - y) * (s : C) + (p : C) * (x * y * (r : C)) := by
    linear_combination hr' + hs'
  rw [e]
  refine v.map_add_le ?_ ?_
  · rw [map_mul]
    exact (mul_le_of_le_one_right' s.2).trans h
  · rw [map_mul]
    refine mul_le_of_le_one_right' ?_
    rw [map_mul, map_mul]
    exact mul_le_one' (mul_le_one' hx hy) r.2

section

variable {C : Type} [Field C] {v : Valuation C NNReal} {R : Type} [CommRing R] [Algebra R C]

theorem mem_pInt [CharZero C] (hv : v.Integers R) {p : ℕ} (hp : p ≠ 0) (x : C) :
    x ∈ pInt (C := C) R p ↔ v x ≤ v (p : C) := by
  have h0 : (p : C) ≠ 0 := Nat.cast_ne_zero.2 hp
  rw [pInt, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨r, rfl⟩
    rw [Algebra.smul_def, map_mul]
    exact mul_le_of_le_one_left' (hv.map_le_one r)
  · intro h
    have h1 : v (x / p) ≤ 1 := by
      rw [map_div₀]
      exact div_le_one_of_le₀ h zero_le
    obtain ⟨r, hr⟩ := hv.exists_of_le_one h1
    exact ⟨r, by rw [Algebra.smul_def, hr, div_mul_cancel₀ _ h0]⟩

theorem val_le_one (hv : v.Integers R) {N : Type} [AddCommGroup N] [Fintype N] [DecidableEq N]
    (AA : HopfOrder (C := C) R N) {g : N → C} (hg : g ∈ AA.carrier) (x : N) : v (g x) ≤ 1 := by
  obtain ⟨r, hr⟩ := AA.le_int hg x
  rw [← hr]
  exact hv.map_le_one r

theorem pow_mem {N : Type} [AddCommGroup N] [Fintype N] [DecidableEq N]
    (AA : HopfOrder (C := C) R N) {g : N → C} (hg : g ∈ AA.carrier) (k : ℕ) :
    g ^ k ∈ AA.carrier := by
  induction k with
  | zero => rw [pow_zero]; exact AA.one_mem
  | succ k ih => rw [pow_succ]; exact AA.mul_mem _ _ ih hg

theorem pow_congr (p : ℕ) [hp : Fact p.Prime] {x z : C} (hx : v x ≤ 1)
    (h : v (z - x) ≤ v (p : C)) : v (z ^ p - x ^ p) ≤ v (p : C) := by
  have := powadd p C v x 0 z hx (by simp) (by simpa using h)
  simpa [zero_pow hp.out.ne_zero] using this

end

theorem a_pow : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (N : Type) [AddCommGroup N] [Module F N] [Fintype N] [DecidableEq N] (AA : HopfOrder (C := C) R N), FStable F AA.carrier → ∀ (K : Submodule F N) (t : N) (τ : MulChar F R) (c : R), c ∈ idealD p AA.carrier K t τ → c ^ p ∈ idealD p AA.carrier K t (τ ^ p) := by
  intro p hp C _ _ _ v R _ _ hv hp1 F _ _ _ _ f hF N _ _ _ _ AA hst K t τ c hc
  obtain ⟨g, ⟨hg, hadd⟩, h1, h2, h3⟩ := hc
  have hp0 := hp.out.ne_zero
  have hb := val_le_one hv AA hg
  refine ⟨g ^ p, ⟨pow_mem AA hg p, fun x y => ?_⟩, fun a x => ?_, fun k hk => ?_, ?_⟩
  · rw [mem_pInt hv hp0]
    exact powadd p C v _ _ _ (hb x) (hb y) ((mem_pInt hv hp0 _).1 (hadd x y))
  · rw [mem_pInt hv hp0, MulChar.pow_apply' _ hp0, map_pow, Pi.pow_apply, Pi.pow_apply, ← mul_pow]
    refine pow_congr p ?_ ((mem_pInt hv hp0 _).1 (h1 a x))
    rw [map_mul]
    exact mul_le_one' (hv.map_le_one _) (hb x)
  · rw [mem_pInt hv hp0]
    have := pow_congr (v := v) p (x := 0) (z := g k) (by simp)
      (by simpa using (mem_pInt hv hp0 _).1 (h2 k hk))
    simpa [zero_pow hp0] using this
  · rw [mem_pInt hv hp0, map_pow, Pi.pow_apply]
    exact pow_congr p (hv.map_le_one _) ((mem_pInt hv hp0 _).1 h3)

end PositivityTheory.HtPt.Rd
end

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.RbTriang
section
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

namespace PositivityTheory.HtPt.Rb

theorem triang_strong (C : Type) [Field C] (v : Valuation C NNReal) (R : Type) [CommRing R]
    [Algebra R C] (hv : v.Integers R) (n : ℕ) (L : Submodule R (Fin n → R)) (hL : L.FG) :
    ∃ d : Fin n → R, (∀ i c, c ∈ Ideal.span {d i} ↔ ∃ l ∈ L, (∀ j, j < i → l j = 0) ∧ l i = c) ∧
      HasLen v R ((Fin n → R) ⧸ L) (∏ i, v (algebraMap R C (d i))) := by
  classical
  haveI : IsDomain R := hv.hom_inj.isDomain
  haveI : ValuationRing R := ValuationRing.of_integers v hv
  obtain ⟨m, w, hw⟩ := Submodule.fg_iff_exists_fin_generating_family.1 hL
  let ψ : (Fin m → R) →ₗ[R] (Fin n → R) := Fintype.linearCombination R w
  have hψ : LinearMap.range ψ = L := by rw [Fintype.range_linearCombination, hw]
  have key : ∀ i : Fin n, ∃ d : R,
      ∀ c, c ∈ Ideal.span {d} ↔ ∃ l ∈ L, (∀ j, j < i → l j = 0) ∧ l i = c := by
    intro i
    let π : (Fin n → R) →ₗ[R] ({j : Fin n // j < i} → R) := LinearMap.funLeft R R Subtype.val
    have h1 := comap_fg_of_valuationRing R (Fin m) {j : Fin n // j < i} (π ∘ₗ ψ) ⊥
      Submodule.fg_bot
    have h2 : Ideal.FG (R := R) (((⊥ : Submodule R _).comap (π ∘ₗ ψ)).map
        (LinearMap.proj i ∘ₗ ψ)) := h1.map _
    obtain ⟨d, hd⟩ := (IsBezout.isPrincipal_of_FG _ h2).principal
    refine ⟨d, fun c => ?_⟩
    have : Ideal.span {d} = ((⊥ : Submodule R _).comap (π ∘ₗ ψ)).map
        (LinearMap.proj i ∘ₗ ψ) := hd.symm
    rw [this]
    constructor
    · rintro ⟨a, ha, rfl⟩
      refine ⟨ψ a, hψ ▸ LinearMap.mem_range_self ψ a, fun j hj => ?_, rfl⟩
      exact congrFun (show π (ψ a) = 0 from ha) ⟨j, hj⟩
    · rintro ⟨l, hl, h0, rfl⟩
      rw [← hψ] at hl
      obtain ⟨a, rfl⟩ := hl
      refine ⟨a, ?_, rfl⟩
      show π (ψ a) = 0
      funext j
      exact h0 j.1 j.2
  choose d hd using key
  refine ⟨d, hd, ?_⟩
  choose u huL hu0 hud using fun i => (hd i (d i)).1 (Ideal.mem_span_singleton_self _)
  let X : Matrix (Fin n) (Fin n) R := Matrix.of fun j i => u i j
  have hcol : ∀ i, u i ∈ LinearMap.range X.mulVecLin := fun i =>
    ⟨Pi.single i 1, by ext j; simp [X]⟩
  have hrange : LinearMap.range X.mulVecLin = L := by
    apply le_antisymm
    · rintro _ ⟨a, rfl⟩
      have : X.mulVecLin a = ∑ i, a i • u i := by
        ext j
        simp [X, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
      rw [this]
      exact L.sum_mem fun i _ => L.smul_mem _ (huL i)
    · have hind : ∀ t : ℕ, ∀ l ∈ L, (∀ j : Fin n, (j : ℕ) + t < n → l j = 0) →
          l ∈ LinearMap.range X.mulVecLin := by
        intro t
        induction t with
        | zero =>
          intro l _ h0
          have : l = 0 := funext fun j => h0 j (by simp)
          rw [this]
          exact Submodule.zero_mem _
        | succ t ih =>
          intro l hl h0
          by_cases ht : t < n
          · let i : Fin n := ⟨n - 1 - t, by omega⟩
            have hi : (i : ℕ) = n - 1 - t := rfl
            have hlow : ∀ j, j < i → l j = 0 := fun j hj => h0 j (by
              have := Fin.lt_def.1 hj
              omega)
            obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 ((hd i (l i)).2 ⟨l, hl, hlow, rfl⟩)
            have h3 := ih (l - c • u i) (L.sub_mem hl (L.smul_mem _ (huL i))) (fun j hj => by
              rcases lt_or_eq_of_le (show j ≤ i from Fin.le_def.2 (by omega)) with h | h
              · simp [hlow j h, hu0 i j h]
              · subst h
                simp [hud, hc])
            have h4 := Submodule.add_mem _ h3 (Submodule.smul_mem _ c (hcol i))
            simpa using h4
          · exact ih l hl fun j hj => by omega
      intro l hl
      exact hind n l hl fun j hj => by omega
  have hdet : X.det = ∏ i, d i := by
    rw [Matrix.det_of_lowerTriangular X (fun j i h => hu0 i j h)]
    exact Finset.prod_congr rfl fun i _ => hud i
  have := Smith.hasLen_coker_det hv X
  rw [hrange, hdet, map_prod, map_prod] at this
  exact this

theorem triang : ∀ (C : Type) [Field C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → ∀ (n : ℕ) (L : Submodule R (Fin n → R)), L.FG → ∃ d : Fin n → R, (∀ i c, c ∈ Ideal.span {d i} ↔ ∃ l ∈ L, (∀ j, j < i → l j = 0) ∧ l i = c) ∧ ((∀ i, d i ≠ 0) → HasLen v R ((Fin n → R) ⧸ L) (∏ i, v (algebraMap R C (d i)))) := by
  intro C _ v R _ _ hv n L hL
  obtain ⟨d, h1, h2⟩ := triang_strong C v R hv n L hL
  exact ⟨d, h1, fun _ => h2⟩

end PositivityTheory.HtPt.Rb
end

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.RdBase
section
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

namespace PositivityTheory.HtPt.Rd

variable {C : Type} [Field C] {v : Valuation C NNReal} {R : Type} [CommRing R] [Algebra R C]
  {F : Type} [Field F]

theorem mem_aug {X : Type} [AddCommGroup X] {M : Submodule R (X → C)} {g : X → C} :
    g ∈ augIdeal M ↔ g ∈ M ∧ g 0 = 0 := Iff.rfl

section Pull

variable {X Y : Type} [AddCommGroup X] [Module F X] [AddCommGroup Y] [Module F Y]

theorem eig_zero {M : Submodule R (X → C)} {χ : MulChar F R} {g : X → C} (hg : g ∈ eig M χ) :
    g 0 = 0 := by
  have := hg.2 0 0
  rwa [smul_zero, MulChar.map_zero, map_zero, zero_mul] at this

theorem eig_pull (u : X →ₗ[F] Y) {M : Submodule R (Y → C)} {M' : Submodule R (X → C)}
    (h : ∀ g ∈ M, g ∘ u ∈ M') {χ : MulChar F R} {g : Y → C} (hg : g ∈ eig M χ) :
    g ∘ u ∈ eig M' χ :=
  ⟨h g hg.1, fun a x => by simpa using hg.2 a (u x)⟩

theorem sq_pull (u : X →ₗ[F] Y) {M : Submodule R (Y → C)} {M' : Submodule R (X → C)}
    (h : ∀ g ∈ M, g ∘ u ∈ M') {g : Y → C} (hg : g ∈ sqIdeal (augIdeal M)) :
    g ∘ u ∈ sqIdeal (augIdeal M') := by
  have : (sqIdeal (augIdeal M)).map (LinearMap.funLeft R C u) ≤ sqIdeal (augIdeal M') := by
    rw [sqIdeal, Submodule.map_span_le]
    rintro _ ⟨a, ha, b, hb, rfl⟩
    refine Submodule.subset_span ⟨a ∘ u, ⟨h a ha.1, ?_⟩, b ∘ u, ⟨h b hb.1, ?_⟩, rfl⟩
    · show a (u 0) = 0
      rw [map_zero]; exact ha.2
    · show b (u 0) = 0
      rw [map_zero]; exact hb.2
  exact this (Submodule.mem_map_of_mem hg)

theorem hasLen_transport (e : X ≃ₗ[F] Y) {M : Submodule R (Y → C)} {M' : Submodule R (X → C)}
    (h : ∀ g, g ∈ M ↔ g ∘ e ∈ M') {χ : MulChar F R} {x : NNReal}
    (hx : HasLen v R (OmType M' χ) x) : HasLen v R (OmType M χ) x := by
  have h1 : ∀ g ∈ M, g ∘ (e : X →ₗ[F] Y) ∈ M' := fun g hg => (h g).1 hg
  have c1 : ∀ g : X → C, (g ∘ (e.symm : Y →ₗ[F] X)) ∘ e = g := fun g => by
    funext x; simp
  have c2 : ∀ g : Y → C, (g ∘ e) ∘ (e.symm : Y →ₗ[F] X) = g := fun g => by
    funext x; simp
  have h2 : ∀ g ∈ M', g ∘ (e.symm : Y →ₗ[F] X) ∈ M := fun g hg => by
    rw [h, c1]; exact hg
  let φ : eig M χ ≃ₗ[R] eig M' χ :=
    { toFun := fun g => ⟨g.1 ∘ e, eig_pull (e : X →ₗ[F] Y) h1 g.2⟩
      invFun := fun g => ⟨g.1 ∘ (e.symm : Y →ₗ[F] X), eig_pull _ h2 g.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun g => Subtype.ext (c2 g.1)
      right_inv := fun g => Subtype.ext (c1 g.1) }
  obtain ⟨m, c, ⟨ψ⟩, hx⟩ := hx
  refine ⟨m, c, ⟨(Submodule.Quotient.equiv _ _ φ ?_).trans ψ⟩, hx⟩
  ext g
  rw [Submodule.mem_map_equiv]
  constructor
  · intro hg
    have : (g.1 ∘ (e.symm : Y →ₗ[F] X)) ∘ e ∈ sqIdeal (augIdeal M') :=
      sq_pull (e : X →ₗ[F] Y) h1 hg
    rw [c1] at this
    exact this
  · intro hg
    exact sq_pull (e.symm : Y →ₗ[F] X) h2 hg

end Pull

variable {N : Type} [AddCommGroup N] [Module F N]

theorem hasLen_trivial (hv : v.Integers R) [Subsingleton N] {M : Submodule R (N → C)}
    {χ : MulChar F R} {x : NNReal} (hx : HasLen v R (OmType M χ) x) : x = 1 := by
  have : Subsingleton (eig M χ) := ⟨fun a b => Subtype.ext (funext fun y => by
    rw [Subsingleton.elim y 0, eig_zero a.2, eig_zero b.2])⟩
  have : Subsingleton (OmType M χ) := (Submodule.Quotient.mk_surjective _).subsingleton
  refine hasLen_unique hv hx ⟨0, Fin.elim0, ⟨LinearEquiv.ofSubsingleton _ _⟩, by simp⟩

theorem quot_step (M : Submodule R (N → C)) {L K : Submodule F N} (hLK : L ≤ K) (t : N) :
    stepOrder (M.comap (LinearMap.funLeft R C (L.mkQ : N → N ⧸ L))) (K.map L.mkQ) (L.mkQ t) =
      stepOrder M K t := by
  ext h
  constructor
  · rintro ⟨g, ⟨hg, hi⟩, rfl⟩
    refine ⟨g ∘ L.mkQ, ⟨hg, fun x k hk => ?_⟩, ?_⟩
    · show g (L.mkQ (x + k)) = g (L.mkQ x)
      rw [map_add]
      exact hi _ _ (Submodule.mem_map_of_mem hk)
    · funext a
      show g (L.mkQ (a • t)) = g (a • L.mkQ t)
      rw [map_smul]
  · rintro ⟨g, ⟨hg, hi⟩, rfl⟩
    have hsur := L.mkQ_surjective
    have key : ∀ x, g (Function.surjInv hsur (L.mkQ x)) = g x := fun x => by
      have h1 : L.mkQ (Function.surjInv hsur (L.mkQ x) - x) = 0 := by
        rw [map_sub, Function.surjInv_eq hsur, sub_self]
      have h2 : Function.surjInv hsur (L.mkQ x) - x ∈ K :=
        hLK ((Submodule.Quotient.mk_eq_zero L).1 h1)
      have := hi x _ h2
      rwa [add_sub_cancel] at this
    refine ⟨g ∘ Function.surjInv hsur, ⟨?_, ?_⟩, ?_⟩
    · show (fun x => g (Function.surjInv hsur (L.mkQ x))) ∈ M
      simpa only [key] using hg
    · rintro x _ ⟨k, hk, rfl⟩
      obtain ⟨x, rfl⟩ := hsur x
      show g (Function.surjInv hsur (L.mkQ x + L.mkQ k)) = g (Function.surjInv hsur (L.mkQ x))
      rw [← map_add, key, key]
      exact hi x k hk
    · funext a
      show g (Function.surjInv hsur (a • L.mkQ t)) = g (a • t)
      rw [← map_smul, key]

theorem sub_stepRes (M : Submodule R (N → C)) {L K : Submodule F N} (hKL : K ≤ L) (t : L) :
    stepOrderRes (M.map (LinearMap.funLeft R C (Subtype.val : L → N))) (K.comap L.subtype) t =
      stepOrderRes M K (t : N) := by
  ext h
  constructor
  · rintro ⟨_, ⟨g, hg, rfl⟩, e⟩
    exact ⟨g, hg, fun a k hk => e a ⟨k, hKL hk⟩ hk⟩
  · rintro ⟨g, hg, e⟩
    exact ⟨_, ⟨g, hg, rfl⟩, fun a k hk => e a k hk⟩

theorem hasLen_line (M : Submodule R (N → C)) {t : N} (ht : t ≠ 0) {χ : MulChar F R} {x : NNReal}
    (hx : HasLen v R (OmType (stepOrder M (⊥ : Submodule F N) t) χ) x) :
    HasLen v R (OmType (M.map (LinearMap.funLeft R C
      (Subtype.val : Submodule.span F {t} → N))) χ) x := by
  refine hasLen_transport (LinearEquiv.toSpanNonzeroSingleton F N t ht) (fun g => ?_) hx
  constructor
  · rintro ⟨g, hg, rfl⟩
    refine ⟨g, ⟨hg, fun x k hk => ?_⟩, rfl⟩
    obtain rfl : k = 0 := hk
    rw [add_zero]
  · rintro ⟨g', ⟨hg, -⟩, e⟩
    refine ⟨g', hg, ?_⟩
    funext y
    obtain ⟨a, rfl⟩ := (LinearEquiv.toSpanNonzeroSingleton F N t ht).surjective y
    exact congrFun e a

end PositivityTheory.HtPt.Rd
end

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.RhPull
section
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

namespace PositivityTheory.HtPt.Rh

theorem sub_pull : ∀ (p : ℕ) (C : Type) [Field C] (R : Type) [CommRing R] [Algebra R C] (N N' : Type) [AddCommGroup N] [AddCommGroup N'] (M : Submodule R (N → C)) (M' : Submodule R (N' → C)) (j : N →+ N') (K : AddSubgroup N), M'.map (LinearMap.funLeft R C (j : N → N')) = invFun M K → GenAF p M' ⊥ → GenAF p M K := by
  intro p C _ R _ _ N N' _ _ M M' j K hM hG g hg
  rw [← hM] at hg
  obtain ⟨g', hg', rfl⟩ := hg
  have hinv : g' ∈ invFun M' ⊥ := ⟨hg', fun x k hk => by rw [AddSubgroup.mem_bot.1 hk, add_zero]⟩
  have h1 : g' ∈ Algebra.adjoin R ((afFun p (invFun M' ⊥) : Submodule R (N' → C)) : Set (N' → C)) :=
    hG hinv
  change (fun x => g' (j x)) ∈
    Algebra.adjoin R ((afFun p (invFun M K) : Submodule R (N → C)) : Set (N → C))
  clear hg' hinv
  induction h1 using Algebra.adjoin_induction with
  | mem f hf =>
    refine Algebra.subset_adjoin ⟨?_, fun x y => ?_⟩
    · rw [← hM]
      exact ⟨f, hf.1.1, rfl⟩
    · have := hf.2 (j x) (j y)
      simpa only [map_add] using this
  | algebraMap r => exact Subalgebra.algebraMap_mem _ r
  | add f f' _ _ h h' => exact Subalgebra.add_mem _ h h'
  | mul f f' _ _ h h' => exact Subalgebra.mul_mem _ h h'

end PositivityTheory.HtPt.Rh
end

