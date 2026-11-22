import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartFH
import ReciprocityTheory.DualLattices.Bundle0026
import ReciprocityTheory.DualLattices.Bundle0015
import ReciprocityTheory.DualLattices.Bundle0033
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.LePreimageOfNil
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import ReciprocityTheory.DualLattices.SubMemOfCompat
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.GenericFiberCubeInclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0002
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.IsEigBasisIff
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0047
import Formalism.LocalToGlobal.CharacterGerms.Bundle0013
import Formalism.LocalToGlobal.CharacterGerms.RowTieSelf
import Formalism.LocalToGlobal.CharacterGerms.Bundle0011
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.HasTeich
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0043
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0034

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsZpRingHomIntegers
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

section
open Polynomial

private theorem zpMap_map_aeval {R' R : Type} [CommRing R'] [CommRing R] (π : R' →+* R)
    (f : ℤ[X]) (x : R') : π (Polynomial.aeval x f) = Polynomial.aeval (π x) f :=
  (Polynomial.aeval_algHom_apply π.toIntAlgHom x f).symm

private theorem zpMap_general {B R : Type} [CommRing B] [CommRing R]
    (f : ℤ[X]) (ζ : B) (S : Submonoid ℕ) (h0 : Polynomial.aeval ζ f = 0)
    (hinj : ∀ g : ℤ[X], Polynomial.aeval ζ g = 0 → f ∣ g)
    (hS : ∀ n ∈ S, IsUnit (n : B))
    (hsurj : ∀ b : B, ∃ n ∈ S, ∃ g : ℤ[X], b * (n : B) = Polynomial.aeval ζ g)
    (hS' : ∀ n ∈ S, IsUnit (n : R)) (z : R) (hz : Polynomial.aeval z f = 0) :
    ∃ β : B →+* R, β ζ = z := by
  let φ : AdjoinRoot f →+* B := AdjoinRoot.lift (algebraMap ℤ B) ζ h0
  let α : AdjoinRoot f →+* R := AdjoinRoot.lift (algebraMap ℤ R) z hz
  have hφ : ∀ g : ℤ[X], φ (AdjoinRoot.mk f g) = Polynomial.aeval ζ g := fun g =>
    AdjoinRoot.lift_mk _ _
  have hα : ∀ g : ℤ[X], α (AdjoinRoot.mk f g) = Polynomial.aeval z g := fun g =>
    AdjoinRoot.lift_mk _ _
  letI : Algebra (AdjoinRoot f) B := φ.toAlgebra
  have halg : algebraMap (AdjoinRoot f) B = φ := rfl
  let S' : Submonoid (AdjoinRoot f) := S.map (Nat.castRingHom (AdjoinRoot f))
  haveI : IsLocalization S' B := by
    refine (isLocalization_iff _ _).mpr ⟨?_, fun b => ?_, fun {a c} h => ⟨1, ?_⟩⟩
    · rintro ⟨_, n, hn, rfl⟩
      simpa using hS n hn
    · obtain ⟨n, hn, g, hg⟩ := hsurj b
      refine ⟨(AdjoinRoot.mk f g, ⟨_, n, hn, rfl⟩), ?_⟩
      simp only [halg, hφ]
      simpa using hg
    · obtain ⟨a, rfl⟩ := AdjoinRoot.mk_surjective a
      obtain ⟨c, rfl⟩ := AdjoinRoot.mk_surjective c
      rw [halg, hφ, hφ, ← sub_eq_zero, ← map_sub] at h
      rw [AdjoinRoot.mk_eq_mk.mpr (hinj _ h)]
  have hu : ∀ y : S', IsUnit (α y) := by
    rintro ⟨_, n, hn, rfl⟩
    simpa using hS' n hn
  refine ⟨IsLocalization.lift hu, ?_⟩
  have h1 : ζ = algebraMap (AdjoinRoot f) B (AdjoinRoot.mk f Polynomial.X) := by
    rw [halg, hφ, Polynomial.aeval_X]
  rw [h1, IsLocalization.lift_eq, hα, Polynomial.aeval_X]

private def zpMap_S (p : ℕ) : Submonoid ℕ where
  carrier := {n | n ≠ 0 ∧ n.Coprime p}
  mul_mem' := fun ha hb => ⟨mul_ne_zero ha.1 hb.1, Nat.Coprime.mul_left ha.2 hb.2⟩
  one_mem' := ⟨one_ne_zero, Nat.coprime_one_left p⟩

private theorem zpMap_isUnit (p M n : ℕ) (hn : n ∈ zpMap_S p) : IsUnit (n : Geo.Tor.ZP p M) := by
  have hmem : (n : ℂ)⁻¹ ∈ Geo.Tor.ZP p M := Subring.subset_closure (Or.inr ⟨n, hn.2, rfl⟩)
  refine IsUnit.of_mul_eq_one (⟨_, hmem⟩ : Geo.Tor.ZP p M) (Subtype.ext ?_)
  have : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn.1
  simp [this]

private theorem zpMap_surj (p M : ℕ) (x : ℂ) (hx : x ∈ Geo.Tor.ZP p M) :
    ∃ n ∈ zpMap_S p, ∃ g : ℤ[X],
      x * (n : ℂ) = Polynomial.aeval ((Geo.Tor.zetaZP p M : Geo.Tor.ZP p M) : ℂ) g := by
  induction hx using Subring.closure_induction with
  | mem x hx =>
    rcases hx with hx | ⟨n, hn, rfl⟩
    · exact ⟨1, one_mem _, Polynomial.X, by simpa [Geo.Tor.zetaZP] using hx⟩
    · by_cases h : n = 0
      · exact ⟨1, one_mem _, 0, by simp [h]⟩
      · have : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr h
        exact ⟨n, ⟨h, hn⟩, 1, by simp [this]⟩
  | zero => exact ⟨1, one_mem _, 0, by simp⟩
  | one => exact ⟨1, one_mem _, 1, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨n, hn, g, hg⟩ := hx
    obtain ⟨m, hm, k, hk⟩ := hy
    refine ⟨n * m, mul_mem hn hm, g * (m : ℤ[X]) + k * (n : ℤ[X]), ?_⟩
    simp only [map_add, map_mul, map_natCast, Nat.cast_mul, ← hg, ← hk]
    ring
  | neg x _ hx =>
    obtain ⟨n, hn, g, hg⟩ := hx
    exact ⟨n, hn, -g, by rw [map_neg, ← hg, neg_mul]⟩
  | mul x y _ _ hx hy =>
    obtain ⟨n, hn, g, hg⟩ := hx
    obtain ⟨m, hm, k, hk⟩ := hy
    refine ⟨n * m, mul_mem hn hm, g * k, ?_⟩
    simp only [map_mul, Nat.cast_mul, ← hg, ← hk]
    ring

private theorem zpMap_unit (p : ℕ) (O : Type) [CommRing O]
    [IsAdicComplete (Ideal.span {(p : O)}) O] (n : ℕ) (hn : n.Coprime p) : IsUnit (n : O) := by
  have hp : (p : O) ∈ Ideal.jacobson (⊥ : Ideal O) :=
    IsAdicComplete.le_jacobson_bot (Ideal.span {(p : O)}) (Ideal.subset_span rfl)
  have hc : IsCoprime (n : O) (p : O) := Nat.Coprime.cast hn
  obtain ⟨a, b, hab⟩ := hc
  have hu := Ideal.mem_jacobson_bot.mp hp (-b)
  have : (p : O) * -b + 1 = a * n := by rw [← hab]; ring
  rw [this] at hu
  exact isUnit_of_mul_isUnit_right hu

private theorem zpMap_main (p : ℕ) (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] (hv : v.Integers O)
    [IsAdicComplete (Ideal.span {(p : O)}) O] (M : ℕ) (hM : M ≠ 0) (hMp : M.Coprime p) :
    ∃ β : Geo.Tor.ZP p M →+* O, Function.Injective β ∧ IsUnit (M : O) ∧
      ∀ (k : Type) [Field k] (gk : O →+* k), IsPrimitiveRoot (gk (β (Geo.Tor.zetaZP p M))) M := by
  have hpos : 0 < M := Nat.pos_of_ne_zero hM
  haveI : NeZero M := ⟨hM⟩
  have hprim : IsPrimitiveRoot ((Geo.Tor.zetaZP p M : Geo.Tor.ZP p M) : ℂ) M :=
    Complex.isPrimitiveRoot_exp M hM
  have hmin := cyclotomic_eq_minpoly hprim hpos
  have hcoe : ∀ g : ℤ[X], ((Polynomial.aeval (Geo.Tor.zetaZP p M) g : Geo.Tor.ZP p M) : ℂ)
      = Polynomial.aeval ((Geo.Tor.zetaZP p M : Geo.Tor.ZP p M) : ℂ) g :=
    fun g => zpMap_map_aeval (Geo.Tor.ZP p M).subtype g _
  have h0 : Polynomial.aeval (Geo.Tor.zetaZP p M) (cyclotomic M ℤ) = 0 := by
    apply Subtype.ext
    rw [hcoe, hmin]
    exact minpoly.aeval _ _
  obtain ⟨w, hw⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot C M
  have hvw : v w ≤ 1 := by
    have h1 : v w ^ M = 1 := by rw [← map_pow, hw.pow_eq_one, map_one]
    exact ((pow_eq_one_iff_of_nonneg zero_le hM).mp h1).le
  obtain ⟨z, rfl⟩ := hv.exists_of_le_one hvw
  have hminw := cyclotomic_eq_minpoly hw hpos
  have hz : Polynomial.aeval z (cyclotomic M ℤ) = 0 := by
    apply hv.hom_inj
    rw [zpMap_map_aeval, map_zero, hminw]
    exact minpoly.aeval _ _
  have hsurj : ∀ b : Geo.Tor.ZP p M, ∃ n ∈ zpMap_S p, ∃ g : ℤ[X],
      b * (n : Geo.Tor.ZP p M) = Polynomial.aeval (Geo.Tor.zetaZP p M) g := by
    intro b
    obtain ⟨n, hn, g, hg⟩ := zpMap_surj p M b b.2
    exact ⟨n, hn, g, Subtype.ext (by rw [hcoe, ← hg]; simp)⟩
  obtain ⟨β, hβ⟩ := zpMap_general (cyclotomic M ℤ) (Geo.Tor.zetaZP p M) (zpMap_S p) h0
    (fun g hg => by
      rw [hmin]
      refine minpoly.isIntegrallyClosed_dvd (hprim.isIntegral hpos) ?_
      rw [← hcoe, hg]
      rfl)
    (zpMap_isUnit p M) hsurj (fun n hn => zpMap_unit p O n hn.2) z hz
  have hMu : IsUnit (M : O) := zpMap_unit p O M hMp
  refine ⟨β, ?_, hMu, ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro b hb
    obtain ⟨n, hn, g, hg⟩ := hsurj b
    have h1 : Polynomial.aeval (algebraMap O C z) g = 0 := by
      rw [← zpMap_map_aeval, ← hβ, ← zpMap_map_aeval, ← hg, map_mul, hb, zero_mul, map_zero]
    have h2 : cyclotomic M ℤ ∣ g := by
      rw [hminw]
      exact minpoly.isIntegrallyClosed_dvd (hw.isIntegral hpos) h1
    obtain ⟨q, rfl⟩ := h2
    rw [map_mul, h0, zero_mul] at hg
    exact ((zpMap_isUnit p M n hn).mul_left_eq_zero).mp hg
  · intro k _ gk
    haveI : NeZero (M : k) := ⟨by simpa using (hMu.map gk).ne_zero⟩
    rw [← isRoot_cyclotomic_iff, hβ, IsRoot.def, ← map_cyclotomic_int, ← algebraMap_int_eq,
      eval_map_algebraMap, ← zpMap_map_aeval, hz, map_zero]

end

theorem exists_zp_ringHom_integers : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (M : ℕ), M ≠ 0 → M.Coprime p → ∃ β : Geo.Tor.ZP p M →+* O, Function.Injective β ∧ IsUnit (M : O) ∧ ∀ (k : Type) [Field k] (gk : O →+* k), IsPrimitiveRoot (gk (β (Geo.Tor.zetaZP p M))) M := by
  intro p _ C _ _ _ v O _ _ hv _ _ M hM hMp
  exact zpMap_main p C v O hv M hM hMp

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.HodgeTateDatumHypothesesPeriodTower
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChF

theorem hodgeTateSetting_ainfTower_of_isPrimitiveRoot : ∀ (p : ℕ) [Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C] {v : Valuation C NNReal} (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (hv : v.Integers O) (ε : PreTilt O p) (hε : IsPrimitiveRoot (((frobeniusEquiv (PreTilt O p) p).symm ε).untilt) p) [Algebra ℤ_[p] O] (OE : Type) [CommRing OE] [StarRing OE], HodgeTateSetting p v O (ℤ_[p] ⊗[ℤ] OE) (sigE p OE) (show O from (Ainf.ainfTowerL p O hv ε hε).c) := by
  intro p hp C _ _ _ v O _ _ hu _ hv ε hε _ OE _ _
  refine ⟨hv, ?_, ?_, ?_, ?_⟩
  · exact lt_of_le_of_ne (hv.map_le_one _) (fun e => hu.out (hv.isUnit_of_one' e))
  · rw [map_natCast]
    exact fun h => Nat.cast_ne_zero.2 hp.out.ne_zero ((Valuation.zero_iff v).1 h)
  · rw [map_natCast]
    exact Ainf.c_val p O hv ε hε
  · intro a
    induction a using TensorProduct.induction_on with
    | zero => simp
    | tmul x y =>
      have h : ∀ (x : ℤ_[p]) (y : OE), sigE p OE (x ⊗ₜ[ℤ] y) = x ⊗ₜ[ℤ] star y := fun _ _ => rfl
      rw [h, h, star_star]
    | add x y hx hy => rw [map_add, map_add, hx, hy]

end GlobalTheory.ChF
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.HopfPointMem
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChF

private theorem hopfPoint_mem {C : Type} [Field C] (R : Type) [CommRing R] [Algebra R C]
    (N : Type) [Unique N] (f : N → C) (hf : f ∈ L2.intFun (C := C) R N) :
    ∃ r : R, f = r • (1 : N → C) := by
  obtain ⟨r, hr⟩ := hf default
  refine ⟨r, funext fun x => ?_⟩
  rw [Subsingleton.elim x default, ← hr]
  simp [Algebra.smul_def]

private theorem hopfPoint_one {C : Type} [Field C] (R : Type) [CommRing R] [Algebra R C]
    (N : Type) : (1 : N → C) ∈ L2.intFun (C := C) R N := fun _ => ⟨1, by simp⟩

private def hopfPoint {C : Type} [Field C] (R : Type) [CommRing R] [Algebra R C]
    (N : Type) [AddCommGroup N] [Fintype N] [DecidableEq N] [Unique N] :
    L2.HopfOrder (C := C) R N where
  carrier := L2.intFun R N
  lat := by
    refine ⟨1, by simp, le_antisymm ?_ ?_⟩
    · intro f hf
      obtain ⟨r, rfl⟩ := hopfPoint_mem R N f hf
      refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨default, ?_⟩)
      funext x
      rw [Subsingleton.elim x default]
      simp
    · rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩ x
      refine ⟨1, ?_⟩
      rw [Subsingleton.elim x j]
      simp
  le_int := le_rfl
  one_mem := hopfPoint_one R N
  mul_mem := by
    intro f g hf hg x
    obtain ⟨r, hr⟩ := hf x
    obtain ⟨s, hs⟩ := hg x
    exact ⟨r * s, by simp [hr, hs]⟩
  comul := by
    intro f hf
    refine Submodule.subset_span ⟨f, hf, 1, hopfPoint_one R N, ?_⟩
    funext q
    change f (q.1 + q.2) = f q.1 * 1
    rw [_root_.mul_one, Subsingleton.elim (q.1 + q.2) q.1]
  antipode := fun f hf x => hf (-x)

theorem htd_dim_zero : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] (OE : Type) [CommRing OE] [StarRing OE] (cp : O), Nonempty (HodgeTateDatum p 0 v O (ℤ_[p] ⊗[ℤ] OE) (sigE p OE) cp) := by
  intro p _ C _ _ _ v O _ _ _ _ _ _ OE _ _ cp
  let _ : Unique (Nb p 0) := Pi.uniqueOfIsEmpty _
  have hS : Subsingleton (LieDualModP p O 0) :=
    (Submodule.Quotient.mk_surjective _).subsingleton
  refine ⟨{
    ρ :=
      { toFun := fun _ => 0
        map_one' := Subsingleton.elim _ _
        map_mul' := fun _ _ => Subsingleton.elim _ _
        map_zero' := Subsingleton.elim _ _
        map_add' := fun _ _ => Subsingleton.elim _ _
        commutes' := fun _ => Subsingleton.elim _ _ }
    ρL :=
      { toFun := fun _ => 0
        map_one' := Subsingleton.elim _ _
        map_mul' := fun _ _ => Subsingleton.elim _ _
        map_zero' := Subsingleton.elim _ _
        map_add' := fun _ _ => Subsingleton.elim _ _ }
    P := 0
    PL := 0
    E := 0
    E_alternating := ⟨Subsingleton.elim _ _, fun _ => rfl⟩
    isUnit_det_E := by simp
    E_equivariant := fun _ => Subsingleton.elim _ _
    projectors := ⟨Subsingleton.elim _ _, Subsingleton.elim _ _, Subsingleton.elim _ _,
      fun _ => Subsingleton.elim _ _, fun _ => Subsingleton.elim _ _⟩
    Ht := 0
    Bt := 0
    Ht_equivariant := ⟨fun _ => Subsingleton.elim _ _, Subsingleton.elim _ _⟩
    form_eq_alt := Subsingleton.elim _ _
    AA := hopfPoint O (Nb p 0)
    h3 := fun a f hf => ⟨f, hf, fun t => congrArg f (Subsingleton.elim _ _)⟩
    h4 := fun k => k.elim0
    h5 := fun _ s => ⟨1, hopfPoint_one O _, fun t => by
      have h0 : Up.pair p 0 0 s t = 0 := by simp [Up.pair]
      rw [h0, map_zero, ZMod.val_zero, pow_zero, Pi.one_apply]⟩
    φ := 0
    cotangent_surjective := fun y => ⟨0, Subsingleton.elim _ _⟩
    cotangent_ker_eq := ?_
    cotangent_linear := fun _ _ _ _ _ _ => Subsingleton.elim _ _ }⟩
  rw [LinearMap.ker_zero, eq_comm, eq_top_iff]
  intro f _
  have : f = 0 := by
    apply Subtype.ext
    funext x
    rw [Subsingleton.elim x 0]
    exact f.2.2
  rw [this]
  exact Submodule.zero_mem _

end GlobalTheory.ChF
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.InvariantDerivationsConstantInLogCoordinatesStatement
section
open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw GlobalTheory.RowVal ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.invariantDerivations_constant_in_logCoordinates : ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ) (Y : FBChart C V O dd) (n : ℕ) (W : Type) [Fintype W] (Z : Fin n × Fin dd → MvPowerSeries W C), (∀ s, MvPowerSeries.constantCoeff (Z s) = 0) → ∀ (b : Fin n) (u : Fin dd → C) (co : W → C), (∀ (b' : Fin n) (j : Fin dd), ∑ w, co w • MvPowerSeries.pderiv C w (Z (b', j)) = if b' = b then MvPowerSeries.C (u j) else 0) → ∀ G : PS C n dd, MvPowerSeries.subst (fun s : Fin n × Fin dd => MvPowerSeries.subst (fun j : Fin dd => Z (s.1, j)) (un1 (Y.ex s.2))) (DofN (Y.B.FK C) b u G) = ∑ w, co w • MvPowerSeries.pderiv C w (MvPowerSeries.subst (fun s : Fin n × Fin dd => MvPowerSeries.subst (fun j : Fin dd => Z (s.1, j)) (un1 (Y.ex s.2))) G) := by
  first | exact @GlobalTheory.InvDerivLog.subst_ex_DofN | exact GlobalTheory.InvDerivLog.subst_ex_DofN | (intros; apply GlobalTheory.InvDerivLog.subst_ex_DofN <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.IsGaugeAdjointIntegralEndPairAddStatement
section
open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isGaugeAdjointIntegralEndPair_add : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) (I : Fin 2 → Type) (κ : Type) [Fintype κ] (X : RawChart C d I κ), RLaw X V → ∀ M M' N N' : Matrix κ κ C, IsEnd X V M M' → IsEnd X V N N' → IsEnd X V (M + N) (M' + N') := by
  first | exact @GlobalTheory.RowLaw.EndSum.isEnd_add | exact GlobalTheory.RowLaw.EndSum.isEnd_add | (intros; apply GlobalTheory.RowLaw.EndSum.isEnd_add <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.JacobianMulTangentChartMatrixIntertwines
section
set_option autoImplicit false
noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChF

private theorem nv_lin {R S : Type} [CommRing R] [CommRing S] (s : R →+* S) {n d : ℕ} (f : PS R n d)
    (hf : MvPowerSeries.constantCoeff f = 0) (a : Fin n → Fin d → S)
    (h : ∀ i j i' j', a i j * a i' j' = 0) :
    nv s f a = ∑ i, ∑ j, s (MvPowerSeries.coeff (Finsupp.single (i, j) 1) f) * a i j := by
  have ha : ∀ i j, IsNilpotent (a i j) := fun i j => ⟨2, by rw [pow_two, h]⟩
  rw [(nv_calculus R S s n d a ha).2.2.2.2.2 h f, hf, map_zero, zero_add, Fintype.sum_prod_type]

private theorem chart_add {R₀ : Type} [CommRing R₀] {B : BX R₀} {O : LAlg R₀} {g : ℕ} {F : FGLaw (O : Type) g}
    {Y : ∀ R : LAlg R₀, LHom O R → (Fin g → (R : Type)) → B.G R} (hY : BXChart B O F.F Y)
    (R : LAlg R₀) (s : LHom O R) (e : (R : Type)) (he : e * e = 0) (v w : Fin g → (R : Type)) :
    Y R s (fun k => v k * e) + Y R s (fun k => w k * e) = Y R s (fun k => (v k + w k) * e) := by
  have hn : ∀ x : (R : Type), IsNilpotent (x * e) := fun x =>
    ⟨2, by rw [mul_pow, pow_two e, he, mul_zero]⟩
  have hl : ∀ v w : Fin g → (R : Type), Y R s (fun k => v k * e) + Y R s (fun k => w k * e) =
      Y R s (fun k => (∑ j, s.1 (MvPowerSeries.coeff (Finsupp.single (0, j) 1) (F.F k)) * v j +
        ∑ j, s.1 (MvPowerSeries.coeff (Finsupp.single (1, j) 1) (F.F k)) * w j) * e) := by
    intro v w
    rw [hY.law R s _ _ (fun _ => hn _) (fun _ => hn _)]
    congr 1
    funext k
    rw [nv_lin _ _ (F.const k)]
    · simp [Fin.sum_univ_two, add_mul, Finset.sum_mul, _root_.mul_assoc]
    · have hx : ∀ x y : (R : Type), x * e * (y * e) = 0 := fun x y => by
        rw [_root_.mul_mul_mul_comm, he, mul_zero]
      intro i j i' j'
      fin_cases i <;> fin_cases i' <;> exact hx _ _
  have h0 : Y R s (fun k => (0 : Fin g → (R : Type)) k * e) = 0 := by
    simp only [Pi.zero_apply, zero_mul]
    exact hY.zero R s
  have h1 := hl v 0
  have h2 := hl 0 w
  rw [h0, add_zero] at h1
  rw [h0, zero_add] at h2
  have h1' := hY.inj R s _ _ (fun _ => hn _) (fun _ => hn _) h1
  have h2' := hY.inj R s _ _ (fun _ => hn _) (fun _ => hn _) h2
  rw [hl]
  congr 1
  funext k
  have e1 := congrFun h1' k
  have e2 := congrFun h2' k
  simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero, add_zero, zero_add] at e1 e2
  rw [add_mul, add_mul, e1, e2]

private theorem chart_sum {R₀ : Type} [CommRing R₀] {B : BX R₀} {O : LAlg R₀} {g : ℕ} {F : FGLaw (O : Type) g}
    {Y : ∀ R : LAlg R₀, LHom O R → (Fin g → (R : Type)) → B.G R} (hY : BXChart B O F.F Y)
    (R : LAlg R₀) (s : LHom O R) (e : (R : Type)) (he : e * e = 0) {κ : Type} (t : Finset κ)
    (v : κ → Fin g → (R : Type)) :
    ∑ i ∈ t, Y R s (fun k => v i k * e) = Y R s (fun k => (∑ i ∈ t, v i k) * e) := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty, zero_mul]
    exact (hY.zero R s).symm
  | insert a t ha ih =>
    rw [Finset.sum_insert ha, ih, chart_add hY R s e he]
    simp only [Finset.sum_insert ha]

theorem lin_mul_tanMat : ∀ (R₀ : Type) [CommRing R₀] (B : BX R₀) (O : LAlg R₀) (g : ℕ) (F : FGLaw (O : Type) g) (Y : ∀ R : LAlg R₀, LHom O R → (Fin g → (R : Type)) → B.G R), BXChart B O F.F Y → ∀ (gb : Module.Basis (Fin g) R₀ B.gg) (S : Matrix (Fin g) (Fin g) (O : Type)), TanMat B O Y gb S → ∀ (A : OEnd B O) (α : Fin g → PS (O : Type) 1 g) (ρ : Matrix (Fin g) (Fin g) (O : Type)), (∀ j, MvPowerSeries.constantCoeff (α j) = 0) → (∀ (R : LAlg R₀) (s : LHom O R) (a : Fin g → (R : Type)), (∀ i, IsNilpotent (a i)) → A.f s (Y R s a) = Y R s (fun j => nv s.1.toRingHom (α j) ![a])) → (∀ {R S : LAlg R₀} (s : LHom O R) (π : LHom R S) (hπ : π.SqZero) (l : Fin g) (i : π.ker) (m : Fin g → π.ker), (∀ k, (m k : (R : Type)) = s.1 (ρ k l) * i) → A.f s (B.tg π hπ (gb l ⊗ₜ[R₀] i)) = B.tg π hπ (∑ k, gb k ⊗ₜ[R₀] m k)) → lin α * S = S * ρ := by
  intro R₀ _ B O g F Y hY gb S hS A α ρ hα hA hρ
  let Dp : DualPair O := DualNum.dualPair O
  have hπ : Dp.π.SqZero := Dp.π.sqZero_of_span Dp.η (fun r => ⟨Dp.σ.1 r, Dp.sect r⟩) Dp.ker_eq Dp.η_sq
  have hn : ∀ x : (Dp.D : Type), IsNilpotent (x * Dp.η) := fun x =>
    ⟨2, by rw [mul_pow, pow_two Dp.η, Dp.η_sq, mul_zero]⟩
  have hη : Dp.η ∈ Dp.π.ker := by simpa using Dp.ση_mem 1
  ext j l
  have h := hρ Dp.σ Dp.π hπ l ⟨Dp.η, hη⟩ (fun k => ⟨Dp.σ.1 (ρ k l) * Dp.η, Dp.ση_mem _⟩) (fun _ => rfl)
  rw [map_sum, hS _ _ Dp.σ, hA _ _ _ (fun _ => hn _)] at h
  simp only [hS _ _ Dp.σ, ← _root_.mul_assoc] at h
  rw [chart_sum hY _ _ _ Dp.η_sq] at h
  have hv : (fun j => nv Dp.σ.1.toRingHom (α j) ![fun k => Dp.σ.1 (S k l) * Dp.η]) =
      fun j => Dp.σ.1 ((lin α * S) j l) * Dp.η := by
    funext j
    rw [nv_lin _ _ (hα j)]
    · simp [Matrix.mul_apply, lin, Finset.sum_mul, _root_.mul_assoc]
    · intro i j i' j'
      fin_cases i; fin_cases i'
      show Dp.σ.1 _ * Dp.η * (Dp.σ.1 _ * Dp.η) = 0
      rw [_root_.mul_mul_mul_comm, Dp.η_sq, mul_zero]
  rw [hv] at h
  have h2 := congrFun (hY.inj _ _ _ _ (fun _ => hn _) (fun _ => hn _) h) j
  rw [← sub_eq_zero]
  apply Dp.free
  rw [map_sub, sub_mul, h2, Matrix.mul_apply, map_sum]
  simp only [map_mul, sub_self]

end GlobalTheory.ChF
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.JetAt0ProdSubstDisjointVariablesStatement
section
open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw GlobalTheory.RowVal ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jetAt0_prod_subst_disjoint_variables : ∀ (C : Type) [Field C] (Orb : Type) [Fintype Orb] (σ : Orb → Type) [∀ o, Fintype (σ o)] (τ : Type) (e : ∀ o, σ o → τ), Function.Injective (fun x : (Σ o, σ o) => e x.1 x.2) → ∀ (P : ∀ o, MvPolynomial (σ o) C) (F : ∀ o, MvPowerSeries (σ o) C), jetAt0 (∏ o, MvPolynomial.rename (e o) (P o)) (∏ o, MvPowerSeries.subst (fun x : σ o => (MvPowerSeries.X (e o x) : MvPowerSeries τ C)) (F o)) = ∏ o, jetAt0 (P o) (F o) := by
  first | exact @GlobalTheory.JetProdSubst.jetAt0_prod_subst | exact GlobalTheory.JetProdSubst.jetAt0_prod_subst | (intros; apply GlobalTheory.JetProdSubst.jetAt0_prod_subst <;> assumption)
end

