import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0749
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0041
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0567
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0023
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsPsiCoordOfIsPsiCoord
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0742
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0676
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0699
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0729
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0738
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChoiceSide
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0733
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0740
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0672

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ComplexTypePlaceCharacterEqSuperdiagAddCharMulLo
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

namespace GlobalTheory.XUniRead

section Loc
variable {L : Type} [Field L] [NumberField L] [IsCMField L]

private theorem red_zero (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) {q : ℕ} (hq : q.Prime)
    (red : v.adicCompletionIntegers (maximalRealSubfield L) →+* ZMod q)
    (y : v.adicCompletionIntegers (maximalRealSubfield L))
    (hy : Valued.v (y : v.adicCompletion (maximalRealSubfield L)) < 1) : red y = 0 := by
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : CharZero (v.adicCompletion (maximalRealSubfield L)) :=
    charZero_of_injective_algebraMap (algebraMap (maximalRealSubfield L) _).injective
  have hp : (RingHom.ker red).IsPrime := RingHom.ker_isPrime red
  have hne : RingHom.ker red ≠ ⊥ := by
    intro h
    have h1 : ((q : ℕ) : v.adicCompletionIntegers (maximalRealSubfield L)) ∈ RingHom.ker red := by
      rw [RingHom.mem_ker, map_natCast, ZMod.natCast_self]
    rw [h, Ideal.mem_bot] at h1
    have h2 := congrArg (fun z : v.adicCompletionIntegers (maximalRealSubfield L) =>
      (z : v.adicCompletion (maximalRealSubfield L))) h1
    simp only [SubringClass.coe_natCast, ZeroMemClass.coe_zero, Nat.cast_eq_zero] at h2
    exact hq.ne_zero h2
  have hm : RingHom.ker red = IsLocalRing.maximalIdeal _ :=
    IsLocalRing.eq_maximalIdeal (hp.isMaximal hne)
  rw [← RingHom.mem_ker, hm, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  obtain ⟨z, hz⟩ := hu.exists_right_inv
  have h2 := congrArg (fun z : v.adicCompletionIntegers (maximalRealSubfield L) =>
      Valued.v (z : v.adicCompletion (maximalRealSubfield L))) hz
  simp only [MulMemClass.coe_mul, map_mul, OneMemClass.coe_one, map_one] at h2
  have hz1 : Valued.v (z : v.adicCompletion (maximalRealSubfield L)) ≤ 1 := z.2
  have h3 := mul_le_mul_right hz1 (Valued.v (y : v.adicCompletion (maximalRealSubfield L)))
  rw [h2, mul_one] at h3
  exact absurd hy (not_lt.2 h3)

private theorem intLift_coe (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L)))
    (y : v.adicCompletionIntegers (maximalRealSubfield L)) :
    NX.intLift v (y : v.adicCompletion (maximalRealSubfield L)) = y := by
  unfold NX.intLift
  rw [dif_pos y.2]

private theorem sum_top {R : Type} [CommRing R] {n r : ℕ} (h : r ≤ n) (X : Matrix (Fin n) (Fin n) R) :
    (∑ a : Fin n, ∑ b : Fin n, if a.val + 1 = b.val ∧ b.val < r then X a b else 0) = NX.supSum r (NX.topR h X) := by
  unfold NX.supSum NX.topR
  symm
  refine Finset.sum_of_injOn (Fin.castLE h) (Fin.castLE_injective h).injOn (fun _ _ => Finset.mem_univ _)
    (fun a _ ha => Finset.sum_eq_zero fun b _ => if_neg fun hh => ha ⟨⟨a.val, by omega⟩, by simp, Fin.ext rfl⟩) fun a _ => ?_
  refine Finset.sum_of_injOn (Fin.castLE h) (Fin.castLE_injective h).injOn (fun _ _ => Finset.mem_univ _)
    (fun b _ hb => if_neg fun hh => hb ⟨⟨b.val, hh.2⟩, by simp, Fin.ext rfl⟩) fun b _ => ?_
  refine if_congr ?_ rfl rfl
  simp only [Fin.val_castLE, b.2, and_true]
  exact eq_comm

private theorem supSum_small {R : Type} [CommRing R] {r : ℕ} (h : ¬ 2 ≤ r) (M : Matrix (Fin r) (Fin r) R) :
    NX.supSum r M = 0 := by
  unfold NX.supSum
  exact Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => if_neg (by have := b.2; omega)

private theorem loc_read (s : SplitPlace L) {n r : ℕ} (h : r ≤ n) {q : ℕ} (hq : q.Prime)
    (red : s.v.adicCompletionIntegers (maximalRealSubfield L) →+* ZMod q)
    (x : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) (hx : NG.UniRT s r x) :
    NX.IsUniTri r (NX.redMat s.v red (NX.topR h x.val)) ∧ IsUnit (red (NX.intLift s.v (NX.detT r x.val))) ∧
    ((NX.intLift s.v (NX.detT r x.val) : s.v.adicCompletionIntegers (maximalRealSubfield L)) :
      s.v.adicCompletion (maximalRealSubfield L)) = NG.detDD s r x ∧
    ∃ y : s.v.adicCompletionIntegers (maximalRealSubfield L),
      (y : s.v.adicCompletion (maximalRealSubfield L)) = NG.supDiag s r x ∧
      red y = NX.supSum r (NX.redMat s.v red (NX.topR h x.val)) := by
  obtain ⟨⟨⟨X0, hX0⟩, hll⟩, huni⟩ := hx
  obtain ⟨X, hXu, hX⟩ : ∃ X : Matrix (Fin n) (Fin n) (s.v.adicCompletionIntegers (maximalRealSubfield L)),
      IsUnit X.det ∧ ∀ a b, x.val a b = (X a b : s.v.adicCompletion (maximalRealSubfield L)) :=
    ⟨X0.val, Matrix.isUnits_det_units X0, fun a b => by rw [← hX0]; rfl⟩
  have hr : ∀ a b, NX.redMat s.v red (NX.topR h x.val) a b = red (X (Fin.castLE h a) (Fin.castLE h b)) := fun a b => by
    simp only [NX.redMat, NX.topR, Matrix.submatrix_apply]
    rw [hX, intLift_coe]
  have hd : NX.detT r x.val = ((NX.detT r X : s.v.adicCompletionIntegers (maximalRealSubfield L)) :
      s.v.adicCompletion (maximalRealSubfield L)) := by
    unfold NX.detT
    refine Eq.trans ?_ (RingHom.map_det (s.v.adicCompletionIntegers (maximalRealSubfield L)).subtype _).symm
    congr 1
    exact Matrix.ext fun a b => hX _ _
  refine ⟨⟨fun a b hab => ?_, fun a => ?_⟩, ?_, ?_, NX.supSum r (NX.topR h X), ?_, ?_⟩
  · rw [hr]
    refine red_zero _ hq red _ ?_
    rw [← hX]
    exact (huni _ _ a.2 b.2).1 hab
  · rw [hr, ← sub_eq_zero, ← map_one red, ← map_sub]
    refine red_zero _ hq red _ ?_
    have := (huni (Fin.castLE h a) (Fin.castLE h a) a.2 a.2).2 rfl
    rw [hX] at this
    exact this
  · rw [hd, intLift_coe]
    have h1 := hXu.map red
    rw [RingHom.map_det, Matrix.twoBlockTriangular_det' (red.mapMatrix X) (fun a : Fin n => r ≤ a.val)
      (fun a ha b hb => red_zero _ hq red _ (by rw [← hX]; exact hll a b ha (not_le.1 hb)))] at h1
    have h2 := isUnit_of_mul_isUnit_left h1
    unfold NX.detT
    rw [RingHom.map_det]
    exact h2
  · rw [hd, intLift_coe, ← hd]
    rfl
  · unfold NG.supDiag
    rw [sum_top h]
    unfold NX.supSum
    push_cast
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    split_ifs
    · exact (hX _ _).symm
    · rfl
  · unfold NX.supSum
    simp only [map_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    split_ifs
    · exact (hr _ _).symm
    · exact map_zero _

end Loc

end GlobalTheory.XUniRead

theorem _root_.GlobalTheory.T.complex_typePlaceCharacter_eq_superdiag_addChar_mul_lowerDet : ∀ (D : D7) (X : NExpTied D) (i : D.ntw.Tw) (k : ℕ) (b : Bool) (kv0 : Σ kk : Fin 2, D.nd.PlG kk)
    (s : SplitPlace D.host.E) (red : s.v.adicCompletionIntegers (maximalRealSubfield D.host.E) →+* ZMod (D.host.g kv0.1))
    (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ),
    (∀ (u : G0g D.nd) (hu : u ∈ D.nexp.U) (hu' : u ∈ Formalism.IndefR.NX.U D.nd),
      ((D.nexp.psiU i b ⟨u, hu⟩ : (FractionRing (D.ntw.O i))ˣ) : FractionRing (D.ntw.O i)) =
        GlobalTheory.SeriesTie.sideEmb D.ntw i b ((psiUOf D.nd (NX.xiRed D) θ ⟨u, hu'⟩ : (↥D.LL0)ˣ) : ↥D.LL0)) →
    ∀ (τ : (ZMod (D.host.g kv0.1))ˣ →* (FractionRing (D.ntw.O i))ˣ) (τ' : (ZMod (D.host.g kv0.1))ˣ →* (↥D.LL0)ˣ),
    (∀ x, ((τ x : (FractionRing (D.ntw.O i))ˣ) : FractionRing (D.ntw.O i)) = GlobalTheory.SeriesTie.sideEmb D.ntw i b ((τ' x : (↥D.LL0)ˣ) : ↥D.LL0)) →
    ∀ (e : NX.Kk D i k →+* ℂ), SideRead i b k e →
    ∀ (ψ₀ : AddChar (s.v.adicCompletion (maximalRealSubfield D.host.E)) ℂ),
    (2 ≤ D.R.r → ∀ y : s.v.adicCompletionIntegers (maximalRealSubfield D.host.E),
      ψ₀ (y : s.v.adicCompletion (maximalRealSubfield D.host.E)) =
        embLL0 D ((θ kv0.1 (Multiplicative.ofAdd (NX.xiRed D kv0 * red y)) : (↥D.LL0)ˣ) : ↥D.LL0)) →
    ∀ (ξ : (s.v.adicCompletion (maximalRealSubfield D.host.E))ˣ →* ℂˣ),
    (∀ (y : s.v.adicCompletionIntegers (maximalRealSubfield D.host.E)) (hy : IsUnit (red y))
      (uu : (s.v.adicCompletion (maximalRealSubfield D.host.E))ˣ), (uu : s.v.adicCompletion (maximalRealSubfield D.host.E)) = y →
        ((ξ uu : ℂˣ) : ℂ) = embLL0 D ((τ' hy.unit : (↥D.LL0)ˣ) : ↥D.LL0)) →
    ∀ (x : GL (Fin D.R.nV) (s.v.adicCompletion (maximalRealSubfield D.host.E))), NG.UniRT s D.R.r x →
    ∀ uu : (s.v.adicCompletion (maximalRealSubfield D.host.E))ˣ,
      (uu : s.v.adicCompletion (maximalRealSubfield D.host.E)) = NG.detDD s D.R.r x →
      e (NX.gVal D i k b kv0 s red τ (x : Matrix (Fin D.R.nV) (Fin D.R.nV) (s.v.adicCompletion (maximalRealSubfield D.host.E)))) =
        ψ₀ (NG.supDiag s D.R.r x) * ((ξ uu : ℂˣ) : ℂ) := by
  intro D X i k b kv0 s red θ hpsi τ τ' hτ e he ψ₀ hψ₀ ξ hξ x hx uu huu
  classical
  obtain ⟨h1, h2, h3, y, hy, hry⟩ := GlobalTheory.XUniRead.loc_read s (n := D.R.nV) (Nat.le_add_right D.R.r D.R.t : D.R.r ≤ D.R.nV)
    (D.host.g_prime kv0.1) red x hx
  unfold NX.gVal
  erw [dif_pos h2]
  rw [map_mul, hτ, he, hξ _ h2 uu (huu.trans h3.symm)]
  congr 1
  generalize hM : NX.redMat s.v red (NX.topR (Nat.le_add_right D.R.r D.R.t : D.R.r ≤ D.R.nV) x.val) = M
  erw [hM] at h1 hry
  have hdet : IsUnit M.det := by
    rw [Matrix.det_of_upperTriangular h1.1, Finset.prod_eq_one fun a _ => h1.2 a]
    exact isUnit_one
  have hval := NX.glOf_val M hdet
  generalize hu : (Pi.mulSingle kv0 (NX.glOf M) : G0g D.nd) = u
  have hu0 : (u kv0).val = M := by rw [← hu, Pi.mulSingle_eq_same, hval]
  have hu1 : ∀ kv, kv ≠ kv0 → (u kv).val = 1 := fun kv hkv => by rw [← hu, Pi.mulSingle_eq_of_ne hkv]; rfl
  have hm' : u ∈ Formalism.IndefR.NX.U D.nd := fun kv => by
    by_cases hkv : kv = kv0
    · subst hkv; rw [hu0]; exact h1
    · rw [hu1 kv hkv]; exact ⟨Matrix.blockTriangular_one, fun a => Matrix.one_apply_eq a⟩
  have hm : u ∈ D.nexp.U := by rw [X.U_eq]; exact hm'
  unfold NX.psiUTot
  rw [dif_pos hm, hpsi u hm hm', he, psiUOf_apply, Fintype.prod_eq_single kv0 (fun kv hkv => by
    rw [hu1 kv hkv, NX.supSum_one, mul_zero, ofAdd_zero, map_one]), hu0, ← hy]
  by_cases hr : 2 ≤ D.R.r
  · rw [hψ₀ hr y, hry]
  · have h0 : NG.supDiag s D.R.r x = 0 := by
      unfold NG.supDiag
      exact Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun c _ => if_neg (by omega)
    rw [hy, h0, GlobalTheory.XUniRead.supSum_small hr, mul_zero, ofAdd_zero, map_one, Units.val_one, map_one, AddChar.map_zero_eq_one]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConeConditionsProduct
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

noncomputable section

namespace GlobalTheory.TorRef

theorem psiCoord_associated {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {χ : D.X} {r r' : R}
    (h : PsiCoord D χ r) (h' : PsiCoord D χ r') : Associated r r' := by
  obtain ⟨x, hx, ex⟩ := (GlobalTheory.PeriodFormCompare.psiCoord_iff D χ r).1 h
  obtain ⟨x', hx', ex'⟩ := (GlobalTheory.PeriodFormCompare.psiCoord_iff D χ r').1 h'
  obtain ⟨u, hu⟩ := hx.unique hx'
  have e1 : algebraMap R (FractionRing R) r = algebraMap R (FractionRing R) (u * r') := by
    rw [← ex, hu, map_mul, ← ex']
    rfl
  have e2 : r = u * r' := IsFractionRing.injective R (FractionRing R) e1
  exact ⟨u⁻¹, by rw [e2, mul_comm, ← mul_assoc, Units.inv_mul, one_mul]⟩

theorem inConePull : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R R' : Type) [CommRing R] [IsDomain R] [IsLocalRing R]
    [CommRing R'] [IsDomain R'] [IsLocalRing R'] (φ : R →+* R') (t : SAB H (Sp R)) (t' : SAB H (Sp R'))
    (P : PELUnif (maximalIdeal R) t) (P' : PELUnif (maximalIdeal R') t') (e : P'.D.toPre.X ≃ₗ[𝓞 E] P.D.toPre.X) (m : ℕ)
    (γ : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X),
    (∀ y r, PsiCoord P.D.toPre (e y) r → ∃ u : R'ˣ, PsiCoord P'.D.toPre y (u * φ r)) → InCone P.D.toPre γ →
    InCone P'.D.toPre (fun i => pull e.toLinearMap (γ i)) := by
  intro E _ _ _ H R R' _ _ _ _ _ _ φ t t' P P' e m γ hpsi hin
  intro W _ _ _ hW ϖ hϖ f be hsym hF
  have hF0 : FormAt P.D.toPre (f.comp φ) ϖ (pull e.symm.toLinearMap be) := by
    intro y0
    obtain ⟨r, hr⟩ := (GlobalTheory.PeriodFormCompare.exists_psiCoord_iff P.D.toPre y0).2
      (GlobalTheory.PeriodFormCompare.psiIn_top P.D y0)
    obtain ⟨u, hu⟩ := hpsi (e.symm y0) r (by rwa [e.apply_symm_apply])
    obtain ⟨r', n, hr', hbe, hass⟩ := hF (e.symm y0)
    refine ⟨r, n, hr, by simpa [pull_apply] using hbe, ?_⟩
    have h1 : Associated (u * φ r) r' := psiCoord_associated hu hr'
    have h2 : Associated (f (φ r)) (f (u * φ r)) := by
      rw [map_mul]
      exact ⟨(Units.map f.toMonoidHom u), by simp [mul_comm]⟩
    exact h2.trans ((h1.map f).trans hass)
  obtain ⟨cf, hc, heq⟩ := hin W hW ϖ hϖ (f.comp φ) (pull e.symm.toLinearMap be)
    (fun a b => by simp [pull_apply, hsym]) hF0
  refine ⟨cf, hc, ?_⟩
  refine LinearMap.ext fun a => LinearMap.ext fun b => ?_
  have := congrArg (fun F => F (e a) (e b)) heq
  simpa [toReal, pull_apply, LinearMap.sum_apply] using this

theorem hasCones_of_map : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (X Z : GMod Xo c) (π : Z.X ⟶ X.X) (Cn : ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] (m : ℕ), (Fin m → LinearMap.BilinForm ℤ X) → Prop), (∀ (X₁ X₂ : Type) [AddCommGroup X₁] [Module (𝓞 E) X₁] [Module.Finite (𝓞 E) X₁] [AddCommGroup X₂] [Module (𝓞 E) X₂] [Module.Finite (𝓞 E) X₂] (f : X₁ ≃ₗ[𝓞 E] X₂) (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X₂), Cn X₂ m γ → Cn X₁ m (fun i => pull f.toLinearMap (γ i))) → Z.j ≫ π = X.j → π ≫ X.s = Z.s → HasCones Cn X → HasCones Cn Z := by
  intro E _ _ _ H D l Xo c X Z π Cn hCn hj hs hX z
  obtain ⟨R, _, _, _, ξ, t, a, P, m, γ, hcn, hpt, het, hfu, htor, hcone, hin⟩ := hX (π z)
  obtain ⟨R', _, _, _, ξ', φ, hcn', hpt', het', hfu', hinj, hloc, hsq, hdense⟩ :=
    GlobalTheory.T.formally_unramified_compatible_map E H D l Xo c X Z π hj hs R ξ z hcn het hfu hpt
  obtain ⟨t', a', P', e, htor', hpsi⟩ := pullSt E H R R' φ t P hcn hcn' hinj hloc htor
  obtain ⟨a'', -⟩ := GlobalTheory.ObjMaps.exists_sab_comp a a'
  rw [← hsq] at a''
  obtain ⟨b⟩ := GlobalTheory.T.sabMap_extends_dense E H D l Xo c X Z π hj R' ξ' t' hcn' hdense a''
  exact ⟨R', inferInstance, inferInstance, inferInstance, ξ', t', b, P', m, fun i => pull e.toLinearMap (γ i),
    hcn', hpt', het', hfu', htor', hCn _ _ e m γ hcone, inConePull E H R R' φ t t' P P' e m γ hpsi hin⟩

end GlobalTheory.TorRef
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConeMatchRaysAfterDroppingZeroCoords
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolFan.OrbMark

namespace GlobalTheory.PolFan

theorem cone_match_rays_of_nonneg {X : Type} [AddCommGroup X] {m₀ : ℕ}
    (p : Fin m₀ → LinearMap.BilinForm ℤ X) (t : Fin m₀ → ℝ) (ht : ∀ i, 0 ≤ t i)
    (hp : LinearIndependent ℤ (fun i : {i // 0 < t i} => p i))
    (β : LinearMap.BilinForm ℤ X) (hβ : toReal β = ∑ i, t i • toReal (p i))
    (m : ℕ) (δ : Fin m → LinearMap.BilinForm ℤ X) (hδ : LinearIndependent ℤ δ)
    (c : Fin m → ℝ) (hc : ∀ j, 0 ≤ c j) (hβ' : toReal β = ∑ j, c j • toReal (δ j))
    (h1 : ∀ i, 0 < t i → InRCone δ (p i))
    (h2 : ∀ j, 0 < c j → ∃ a : Fin m₀ → ℝ, (∀ i, 0 ≤ a i) ∧ (∀ i, t i = 0 → a i = 0) ∧
      toReal (δ j) = ∑ i, a i • toReal (p i)) :
    (∀ i, 0 < t i → ∃ j, 0 < c j ∧ ∃ d : ℝ, 0 < d ∧ toReal (p i) = d • toReal (δ j)) ∧
    (∀ j, 0 < c j → ∃ i, 0 < t i ∧ ∃ d : ℝ, 0 < d ∧ toReal (p i) = d • toReal (δ j) ∧
      c j = t i * d) := by
  classical
  set e := (Fintype.equivFin {i // 0 < t i}).symm with he
  have key : ∀ a : Fin m₀ → ℝ, (∀ i, t i = 0 → a i = 0) →
      ∑ i', a (e i') • toReal (p (e i')) = ∑ i, a i • toReal (p i) := by
    intro a ha
    refine Fintype.sum_of_injective (fun i' => ((e i' : {i // 0 < t i}) : Fin m₀))
      (Subtype.val_injective.comp e.injective) _ _ ?_ (fun _ => rfl)
    intro i hi
    have : t i = 0 := by
      by_contra h0
      exact hi ⟨e.symm ⟨i, lt_of_le_of_ne (ht i) (Ne.symm h0)⟩, by simp⟩
    rw [ha i this, zero_smul]
  obtain ⟨r1, r2⟩ := GlobalTheory.T.coneMatch_rays_of_linearIndependent_intForms (fun i' => p (e i')) δ (hp.comp e e.injective) hδ
    (fun i' => t (e i')) c (fun i' => (e i').2) hc
    (by rw [key t (fun _ h => h), ← hβ, hβ'])
    (fun i' => h1 _ (e i').2)
    (fun j hj => by
      obtain ⟨a, ha0, ha1, ha2⟩ := h2 j hj
      exact ⟨fun i' => a (e i'), fun i' => ha0 _, by rw [ha2, ← key a ha1]⟩)
  refine ⟨fun i hi => ?_, fun j hj => ?_⟩
  · simpa using r1 (e.symm ⟨i, hi⟩)
  · obtain ⟨i', h⟩ := r2 j hj
    exact ⟨e i', (e i').2, h⟩

end GlobalTheory.PolFan
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CongrFunHeq
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw
open GlobalTheory.HeightCounting GlobalTheory.Mem.R3.Tr

noncomputable section
namespace GlobalTheory.LayerMove
set_option maxHeartbeats 4000000
variable {D : D7} (m : Mv D)

def Mv.lam (x : GlobalTheory.LamTie.LamDat D) : GlobalTheory.LamTie.LamDat m.D := @_root_.GlobalTheory.LamTie.LamDat.mk (_)
    (C := @_root_.Formalism.L2.Host.CharFrame.mk (_)
      (P := (by with_unfolding_all exact (x.C.P :)))
      (W := (by with_unfolding_all exact (x.C.W :)))
      (mu0 := (by with_unfolding_all exact (x.C.mu0 :)))
      (eta := (by with_unfolding_all exact (x.C.eta :)))
      (chiPsi := (by with_unfolding_all exact (x.C.chiPsi :)))
      (del := (by with_unfolding_all exact (x.C.del :)))
      (del' := (by with_unfolding_all exact (x.C.del' :)))
      (isMu0 := (by with_unfolding_all exact (x.C.isMu0 :)))
      (isEta := (by with_unfolding_all exact (x.C.isEta :)))
      (isChi := (by with_unfolding_all exact (x.C.isChi :)))
      (isDel := (by with_unfolding_all exact (x.C.isDel :)))
      (isDel' := (by with_unfolding_all exact (x.C.isDel' :))))
    (q0 := (by with_unfolding_all exact (x.q0 :)))
    (w0 := (by with_unfolding_all exact (x.w0 :)))
    (c := (by with_unfolding_all exact (x.c :)))
    (chi := (by with_unfolding_all exact (x.chi :)))
theorem Mv.lam_ok {l : GlobalTheory.LamTie.LamDat D} (x : l.Ok) : (m.lam l).Ok := @_root_.GlobalTheory.LamTie.LamDat.Ok.mk (_) (_)
    (places := (by with_unfolding_all exact (x.places :)))
    (aux := (by with_unfolding_all exact (x.aux :)))
    (big := (by with_unfolding_all exact (x.big :)))
theorem Mv.lam_teich {l : GlobalTheory.LamTie.LamDat D} (x : l.Teich) : (m.lam l).Teich := (by with_unfolding_all exact (x :))
theorem Mv.lam_tie {l : GlobalTheory.LamTie.LamDat D} (x : GlobalTheory.LamTie.IsLamTieFull D.ntw l) : GlobalTheory.LamTie.IsLamTieFull m.D.ntw (m.lam l) := (by with_unfolding_all exact (x :))

theorem Mv.rowLoc {D : D7} (m : Mv D) {C : NChoice D} (a : NAllC D C) (F : Formalism.L2.RowFrame D) (F' : Formalism.L2.RowFrame m.D)
    (hF : HEq F'.rep F.rep) (x : Formalism.L2.RowLocTied D a.gal.lp F) : Formalism.L2.RowLocTied m.D (m.all a).gal.lp F' := by
  obtain ⟨rep, inj⟩ := F
  obtain ⟨rep', inj'⟩ := F'
  have e : rep' = (by with_unfolding_all exact (rep :)) := eq_of_heq ((by with_unfolding_all exact (hF :)))
  subst e
  exact (@_root_.Formalism.L2.RowLocTied.mk (_) (_) (_)
    (sat := (by with_unfolding_all exact (x.sat :)))
    )

theorem congrFun_heq {α β : Type} {f g : α → β} (h : HEq f g) (x : α) : f x = g x := by rw [eq_of_heq h]

theorem exists_row (hL : GlobalTheory.Published.LocalLanglandsGL) (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (Wt : Set B.places.Pl) (S' : SStage B w.C Z.W) (N : ∀ u, Submodule (𝓞 B.LL) (Z.V.div.Nu u).V) (h : B.Word → ℝ) (nch : NChoice (w.D Z)) (xd : ThData (w.D Z))
    (p0 : BaseLevelRowSide (w.D Z)) (t : RowsT K w Z Wt p0) (p0' : BaseLevelRowSide (w.D (upL Z S' N h))) (t' : RowsT K w (upL Z S' N h) Wt p0')
    (hs : RowsSame t t') (hg : HEq t'.r.z.geo (R3.Tr.geoHalf (a := ⟨Z.W, Z.V, Z.S, Z.N, Z.G⟩) (upL Z S' N h) (iK := t.r.z.alg) t.r.z.geo))
    (hj : ∀ (μ : (w.D Z).what₂.Tup) (hμ : Formalism.IndefR.RecTie.Used0 (w.D Z) μ) (hμ' : Formalism.IndefR.RecTie.Used0 (w.D (upL Z S' N h)) μ) (i : Fin (w.D Z).R.m) (x : (w.D Z).what₂.Mt μ ((i : ℕ) + 1)), HEq (t'.r.Y.IL.jMt μ hμ' i x).1 (t.r.Y.IL.jMt μ hμ i x).1)
    (hser : ∀ (kKs : ↥t.r.z.core.Q.c.F →+* ↥(w.st Z).toD7.LL0) (hk : ∀ x, ((kKs x : ↥(w.st Z).toD7.LL0) : (w.st Z).toD7.what₂.LL) = algebraMap _ (w.st Z).toD7.what₂.LL x) (YS : Formalism.IndefR.NX.NExpRealS t.r.z.R t.r.z.cG (Formalism.IndefR.NX.ratDatR t.r.z.R t.r.z.cG kKs hk)) (kKs' : ↥t'.r.z.core.Q.c.F →+* ↥(w.st (upL Z S' N h)).toD7.LL0) (hk' : ∀ x, ((kKs' x : ↥(w.st (upL Z S' N h)).toD7.LL0) : (w.st (upL Z S' N h)).toD7.what₂.LL) = algebraMap _ (w.st (upL Z S' N h)).toD7.what₂.LL x) (YS' : Formalism.IndefR.NX.NExpRealS t'.r.z.R t'.r.z.cG (Formalism.IndefR.NX.ratDatR t'.r.z.R t'.r.z.cG kKs' hk')), HEq kKs' kKs → HEq YS'.fi YS.fi → HEq YS'.eF YS.eF → ∀ (a : NAllC (w.D Z) nch) (X' : Formalism.L2.NExpTied (w.st (upL Z S' N h)).toD7), HEq X' ((mvOf w Z S' N h).all a).exp → ∀ (PV : ∀ i : Fin (w.st Z).toD7.R.m, Formalism.IndefR.principalLevelFrame.RowPsi (Formalism.IndefR.Links.Vc (w.st Z).toD7 i) (w.st Z).toD7.R.nV) (PV' : ∀ i : Fin (w.st (upL Z S' N h)).toD7.R.m, Formalism.IndefR.principalLevelFrame.RowPsi (Formalism.IndefR.Links.Vc (w.st (upL Z S' N h)).toD7 i) (w.st (upL Z S' N h)).toD7.R.nV), HEq (fun i => (PV' i).ψ) (fun i => (PV i).ψ) → ∀ Pq Pq', HEq Pq' Pq → SerAt (D := (w.st Z).toD7) YS t.r.z.geo.v₀ a.exp PV (TC.cf w.I w.l Z) Pq → Nonempty (SerAt (D := (w.st (upL Z S' N h)).toD7) YS' t'.r.z.geo.v₀ X' PV' (TC.cf w.I w.l (upL Z S' N h)) Pq'))
    {tp : TupTied (w.D Z) (TC.cf w.I w.l Z) nch} {tp' : TupTied (w.D (upL Z S' N h)) (TC.cf w.I w.l (upL Z S' N h)) (nchUp S' N h nch)}
    (a : NAt hL (w.D Z) (TC.cf w.I w.l Z) nch tp)
    (a' : NAt hL (w.D (upL Z S' N h)) (TC.cf w.I w.l (upL Z S' N h)) (nchUp S' N h nch) tp') (hA : AtSame (mvOf w Z S' N h) a a')
    (r : NRow (D := (w.st Z).toD7) a t.r.z.R t.r.z.F t.r.z.cG t.r.Y) (e : NMore (D := (w.st Z).toD7) r t.r.z.geo xd) :
    ∃ r' : NRow (D := (w.st (upL Z S' N h)).toD7) a' t'.r.z.R t'.r.z.F t'.r.z.cG t'.r.Y,
      Nonempty (NMore (D := (w.st (upL Z S' N h)).toD7) r' t'.r.z.geo (xdUp S' N h xd)) := by
  cases t' with | mk hX' r' exAt' inGeo' grpAt' grp' mu' exact' untw' emt0' emt' etaF' rowInt' idx' => ?_
  cases r' with | mk z' holds' Y' ZZ' tupix' => ?_
  cases z' with | mk Xg' tr' core' alg_eq' R' cG' geo' pins' lev' idG' good' muz' le' ks' => ?_
  rename_i alg'
  have e1 : Xg' = t.r.z.Xg := hs.Xg
  have e2 : tr' = t.r.z.tr := hs.tr
  subst e1 e2
  have e3 : core' = R3.Tr.coreJ (a := ⟨Z.W, Z.V, Z.S, Z.N, Z.G⟩) (upL Z S' N h) t.r.z.core := eq_of_heq hs.core
  subst e3
  have e4 : alg' = t.r.z.alg := by
    apply Algebra.algebra_ext
    intro y
    apply (w.D Z).what₂.embLL.injective
    exact (alg_eq' y).trans (t.r.z.alg_eq y).symm
  subst e4
  have e5 : R' = R3.Tr.real3 (a := ⟨Z.W, Z.V, Z.S, Z.N, Z.G⟩) (upL Z S' N h) (iK := t.r.z.alg) t.r.z.R := eq_of_heq hs.R
  subst e5
  have e6 : cG' = t.r.z.cG := eq_of_heq hs.cG
  subst e6
  have e7 : geo' = (by with_unfolding_all exact ((R3.Tr.geoHalf (a := ⟨Z.W, Z.V, Z.S, Z.N, Z.G⟩) (upL Z S' N h) (iK := t.r.z.alg) t.r.z.geo) :)) := eq_of_heq ((by with_unfolding_all exact (hg :)))
  subst e7
  obtain ⟨nt', all', chr_eq', host', frameN', chrN', chrGal', Pq', Pq_over', pq', jE_eq', mt_eq', Pq_eq', hlow', split', ratIn',
    r1', r2', r3', depth'⟩ := a'
  obtain ⟨s1, s2, s3, s4, s5, s6, s7⟩ := hA
  have e8 : all' = (by with_unfolding_all exact (((mvOf w Z S' N h).all a.all) :)) := eq_of_heq ((by with_unfolding_all exact (s1 :)))
  have e9 : Pq' = (by with_unfolding_all exact (a.Pq :)) := eq_of_heq ((by with_unfolding_all exact (s2 :)))
  subst e8 e9
  obtain ⟨kKs, hk, nexp, hecke, grp, rowLoc, S_eq, hL_eq, rep_eq⟩ := r
  obtain ⟨ad, fi, hrow, cHk, eig, ser, tau, geo, ok, th, xda, large, labc, zeta, pht⟩ := e
  obtain ⟨geo⟩ := geo
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, IL', _, _, _, eFT', _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, ⟨eW', _⟩, _⟩ := Y'
  have e10 : eW' = (by with_unfolding_all exact (t.r.Y.mj.eW :)) := eq_of_heq ((by with_unfolding_all exact (hs.eW :)))
  subst e10
  obtain ⟨Sb, ev, hSb, hev, hE⟩ := eig
  obtain ⟨i1, i2, i3⟩ := s7 ⟨labc, zeta, pht⟩
  obtain ⟨l1, l2, l3, l4, l5, lv⟩ := grp.lvl
  refine Nonempty.elim (hser kKs hk nexp ((by with_unfolding_all exact (kKs :))) ((by with_unfolding_all exact (hk :))) (@_root_.Formalism.IndefR.NX.NExpRealS.mk (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_)
    (fi := (by with_unfolding_all exact (nexp.fi :)))
    (geq := (by with_unfolding_all exact (nexp.geq :)))
    (rho := (by with_unfolding_all exact (nexp.rho :)))
    (chi := (by with_unfolding_all exact (nexp.chi :)))
    (eF := (by with_unfolding_all exact (nexp.eF :)))
    (bsup := kc% nexp.bsup)
    (act := kc% nexp.act)
    )
    ((by with_unfolding_all exact ((HEq.refl kKs) :))) ((by with_unfolding_all exact ((HEq.refl nexp.fi) :))) ((by with_unfolding_all exact ((HEq.refl nexp.eF) :))) a.all ((by with_unfolding_all exact (((mvOf w Z S' N h).all a.all).exp :)))
    ((by with_unfolding_all exact ((HEq.refl ((mvOf w Z S' N h).all a.all).exp) :))) ad.PV (@fun x1 => @_root_.Formalism.IndefR.principalLevelFrame.RowPsi.mk (_) (_) (_)
      (ψ := (by with_unfolding_all exact ((@_root_.GlobalTheory.HeightCounting.MtAd.PV (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) ad ((x1))).ψ : _)))
      (inj := (by with_unfolding_all exact ((@_root_.GlobalTheory.HeightCounting.MtAd.PV (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) ad ((x1))).inj : _)))
      (into := (by with_unfolding_all exact ((@_root_.GlobalTheory.HeightCounting.MtAd.PV (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) ad ((x1))).into : _)))
      (onto := (by with_unfolding_all exact ((@_root_.GlobalTheory.HeightCounting.MtAd.PV (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) ad ((x1))).onto : _))))
    ((by with_unfolding_all exact ((HEq.refl fun i => (ad.PV i).ψ) :))) a.Pq ((by with_unfolding_all exact (a.Pq :))) ((by with_unfolding_all exact ((HEq.refl a.Pq) :))) ser) fun ser' => ?_
  refine ⟨@NRow.mk (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) ((by with_unfolding_all exact (kKs :))) ((by with_unfolding_all exact (hk :)))
    (@_root_.Formalism.IndefR.NX.NExpRealS.mk (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_)
    (fi := (by with_unfolding_all exact (nexp.fi :)))
    (geq := (by with_unfolding_all exact (nexp.geq :)))
    (rho := (by with_unfolding_all exact (nexp.rho :)))
    (chi := (by with_unfolding_all exact (nexp.chi :)))
    (eF := (by with_unfolding_all exact (nexp.eF :)))
    (bsup := kc% nexp.bsup)
    (act := kc% nexp.act)
    )
    (@_root_.Formalism.IndefR.NX.NExpRealH.mk (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_)
    (hL := (by with_unfolding_all exact (hecke.hL :)))
    (hs := (by with_unfolding_all exact (hecke.hs :)))
    (cHk := (by with_unfolding_all exact (hecke.cHk :)))
    (cHk_zero := (by with_unfolding_all exact (hecke.cHk_zero :)))
    (cHk_unit := (by with_unfolding_all exact (hecke.cHk_unit :)))
    (cHk_pow := (by with_unfolding_all exact (hecke.cHk_pow :)))
    (hkEq := kc% hecke.hkEq)
    )
    (@_root_.Formalism.L2.DIV.GrpTie.mk (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_)
    (card := (by with_unfolding_all exact (grp.card :)))
    (e0 := (by with_unfolding_all exact (grp.e0 :)))
    (lvl0 := (by with_unfolding_all exact (grp.lvl0 :)))
    (psi0 := (by with_unfolding_all exact (grp.psi0 :)))
    (idxSharp := (by with_unfolding_all exact (grp.idxSharp :)))
    (lvl := ⟨(by with_unfolding_all exact (l1 :)), (by with_unfolding_all exact (l2 :)), (by with_unfolding_all exact (l3 :)), (by with_unfolding_all exact (l4 :)), (by with_unfolding_all exact (l5 :)),
      ⟨(by with_unfolding_all exact (lv.place :)), (by with_unfolding_all exact (lv.comp :)), (by with_unfolding_all exact (lv.gen :)), (by with_unfolding_all exact (lv.p0 :)), (by with_unfolding_all exact (lv.chi0 :)), (by with_unfolding_all exact (lv.ps :)), (by with_unfolding_all exact (lv.chis :))⟩⟩)
    )
    ((by with_unfolding_all exact (((mvOf w Z S' N h).rowLoc a.all _ (kc% (Formalism.L2.Col.rowFrameOf (w.D (upL Z S' N h)) _ eFT')) (kc% hs.rep) rowLoc) :)))
    (kc% (s3.trans S_eq)) (kc% (s4.trans hL_eq)) (kc% ((s5.trans rep_eq).trans hs.rep.symm)), ⟨@NMore.mk (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_)
    (@_root_.GlobalTheory.HeightCounting.MtAd.mk (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_)
    (PV := @fun x1 => @_root_.Formalism.IndefR.principalLevelFrame.RowPsi.mk (_) (_) (_)
      (ψ := (by with_unfolding_all exact ((@_root_.GlobalTheory.HeightCounting.MtAd.PV (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) ad ((x1))).ψ : _)))
      (inj := (by with_unfolding_all exact ((@_root_.GlobalTheory.HeightCounting.MtAd.PV (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) ad ((x1))).inj : _)))
      (into := (by with_unfolding_all exact ((@_root_.GlobalTheory.HeightCounting.MtAd.PV (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) ad ((x1))).into : _)))
      (onto := (by with_unfolding_all exact ((@_root_.GlobalTheory.HeightCounting.MtAd.PV (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) ad ((x1))).onto : _))))
    (std := (by with_unfolding_all exact (ad.std :)))
    (eW := (by with_unfolding_all exact (ad.eW :)))
    (read := @fun x1 => @fun x2 => @fun x3 => @fun x4 => @fun x5 => kc% ((ad.read (kc% x1) (kc% x2) (kc% x3) (kc% x4) (kc% x5)).trans
      (congrFun_heq (g := (t.r.Y.IL.jMt (kc% x1) (kc% x2) (kc% x3) (kc% x4)).1) (f := kc% (IL'.jMt x1 x2 x3 x4).1)
        (kc% (hj (kc% x1) (kc% x2) (kc% x2) (kc% x3) (kc% x4))) _).symm))
    (rat := (by with_unfolding_all exact (ad.rat :)))
    (wt := (by with_unfolding_all exact (ad.wt :)))
    (id := (by with_unfolding_all exact (ad.id :)))
    )
    ((by with_unfolding_all exact (fi :)))
    (@Formalism.IndefR.NX.NExpHeckeRowX.mk (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) ((by with_unfolding_all exact (hrow.tie :))))
    ((by with_unfolding_all exact (cHk :)))
    ⟨(by with_unfolding_all exact (Sb :)), (by with_unfolding_all exact (ev :)), (by with_unfolding_all exact (hSb :)), (by with_unfolding_all exact ((s6.trans hev) :)), fun i σ k P α Rr hd => (by with_unfolding_all exact ((hE (kc% i) (kc% σ) k (kc% P) (kc% α) (kc% Rr)
      ⟨kc% (@HkDat.split (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) hd), kc% (@HkDat.offS (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) hd),
        kc% (@HkDat.odd (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) hd), kc% (@HkDat.le (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) hd),
        kc% (@HkDat.elt (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) hd), kc% (@HkDat.reps (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) hd)⟩) :))⟩
    ((by with_unfolding_all exact (ser' :))
    )
    ((by with_unfolding_all exact (((mvOf w Z S' N h).tauTrue tau) :)))
    ⟨@_root_.GlobalTheory.GeoTie.ThetaTie.mk (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_)
    (side := @fun x1 => @fun x2 => @fun x3 => @_root_.GlobalTheory.GeoTie.SideTie.mk (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_)
      (pt := (by with_unfolding_all exact ((@_root_.GlobalTheory.GeoTie.ThetaTie.side (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) geo ((x1)) ((x2)) ((x3))).pt : _)))
      (cover := (by with_unfolding_all exact ((@_root_.GlobalTheory.GeoTie.ThetaTie.side (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) geo ((x1)) ((x2)) ((x3))).cover : _)))
      (ev_eq := (by with_unfolding_all exact ((@_root_.GlobalTheory.GeoTie.ThetaTie.side (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) geo ((x1)) ((x2)) ((x3))).ev_eq : _)))
      (fmUr := (by with_unfolding_all exact ((@_root_.GlobalTheory.GeoTie.ThetaTie.side (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) geo ((x1)) ((x2)) ((x3))).fmUr : _)))
      (hk := kc% (@_root_.GlobalTheory.GeoTie.ThetaTie.side (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) geo (kc% x1) (kc% x2) (kc% x3)).hk)
      (hk_none := (by with_unfolding_all exact ((@_root_.GlobalTheory.GeoTie.ThetaTie.side (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) geo ((x1)) ((x2)) ((x3))).hk_none : _))))
    (isUnramified₂ := (by with_unfolding_all exact (geo.isUnramified₂ :)))
    ⟩
    ((by with_unfolding_all exact (ok :))) ((by with_unfolding_all exact (th :))) ((by with_unfolding_all exact (xda :))) ((by with_unfolding_all exact (((mvOf w Z S' N h).large large) :))) ((by with_unfolding_all exact (i1 :))) ((by with_unfolding_all exact (i2 :))) ((by with_unfolding_all exact (i3 :)))⟩⟩

end GlobalTheory.LayerMove
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EigenAdjointOfReadRelationStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.HeightCounting.Fin3
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eigen_adjoint_of_read_relation : ∀ {hL : GlobalTheory.Published.LocalLanglandsGL} {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w} {x : St P} (L : LocAll (lay0 (Dof x))) (l : LC hL x) {p0 : BaseLevelRowSide (w.D (oL x L).Z)} (Y : YT x L p0), YRel L Y → EigAd Y (sbD L l) (eigD L l) := by
  first | exact @GlobalTheory.HeightCounting.Fin3.eigAd_loc | exact GlobalTheory.HeightCounting.Fin3.eigAd_loc | (intros; apply GlobalTheory.HeightCounting.Fin3.eigAd_loc <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsInvariantCarrierDimPolyFanStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_invariant_carrierDim_polyFan : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ) (ψ : InvFun (𝓞 E)), (∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Dominates H.bar X) → IsPolyFan H.bar q ψ → IsTwInv H ψ → ∃ lab : InvFun (𝓞 E), IsTwInv H lab ∧ IsCarrierDim H.bar q ψ lab := by
  first | exact @GlobalTheory.PolFan.CarDim.exists_isCarrierDim | exact GlobalTheory.PolFan.CarDim.exists_isCarrierDim | (intros; apply GlobalTheory.PolFan.CarDim.exists_isCarrierDim <;> assumption)
end

