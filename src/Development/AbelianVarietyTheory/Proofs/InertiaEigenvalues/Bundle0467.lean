import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0401
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0365
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0443
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0373
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0439
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen
import Formalism.LocalToGlobal.ProjectiveLattices.OneLtAbsNormReal
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsRootOfIsAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigIsoCongr
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0006
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0014
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanRingCornerIdealModuleIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0452
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0438
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0442
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0003
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaloisConjOfTeichmullerCongr
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem mem_OC_of_pow_eq {l : ℕ} [Fact l.Prime] {N : ℕ} (hN : 0 < N) (a : ℂ_[l]) (c : OC l)
    (h : a ^ N = (c : ℂ_[l])) : a ∈ 𝓞_ℂ_[l] := by
  rw [GlobalTheory.RingBasics.mem_OC]
  have h1 := (GlobalTheory.RingBasics.mem_OC _).1 c.2
  rw [← h, norm_pow] at h1
  exact (pow_le_one_iff_of_nonneg (norm_nonneg _) hN.ne').1 h1

theorem exists_OC_eq_of_pow_eq {l : ℕ} [Fact l.Prime] {D : Type} [CommRing D] [IsDomain D] (f : OC l →+* D)
    {N : ℕ} (hN : 0 < N) (c : OC l) (r : D) (h : r ^ N = f c) : ∃ s : OC l, f s = r := by
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_pow_nat_eq (c : ℂ_[l]) hN
  haveI : NeZero (N : ℂ_[l]) := ⟨Nat.cast_ne_zero.2 hN.ne'⟩
  haveI : NeZero N := ⟨hN.ne'⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot ℂ_[l] N
  let a' : OC l := ⟨a, mem_OC_of_pow_eq hN a c ha⟩
  let ζ' : OC l := ⟨ζ, mem_OC_of_pow_eq hN ζ 1 hζ.pow_eq_one⟩
  have hζ' : IsPrimitiveRoot ζ' N :=
    IsPrimitiveRoot.of_map_of_injective (f := (𝓞_ℂ_[l]).subtype) hζ Subtype.val_injective
  have ha' : a' ^ N = c := Subtype.ext ha
  have hp := congrArg (Polynomial.eval₂ f r) (X_pow_sub_C_eq_prod hζ' hN ha')
  rw [Polynomial.eval₂_finsetProd, Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C, h,
    sub_self, eq_comm, Finset.prod_eq_zero_iff] at hp
  obtain ⟨i, -, hi⟩ := hp
  rw [Polynomial.eval₂_sub, Polynomial.eval₂_X, Polynomial.eval₂_C, sub_eq_zero] at hi
  exact ⟨_, hi.symm⟩

theorem exists_alg_eq_of_pow_eq {l : ℕ} [Fact l.Prime] {N : ℕ} (hN : 0 < N) (a : Om l) (s : ℂ_[l])
    (h : s ^ N = (a : ℂ_[l])) : ∃ z : Om l, s = (z : ℂ_[l]) := by
  have hf : (Polynomial.X ^ N - Polynomial.C a : Polynomial (Om l)) ≠ 0 :=
    Polynomial.X_pow_sub_C_ne_zero hN a
  have hroot : ((Polynomial.X ^ N - Polynomial.C a : Polynomial (Om l)).map
      (algebraMap (Om l) ℂ_[l])).IsRoot s := by
    simp only [Polynomial.IsRoot, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C,
      Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]
    rw [h]
    exact sub_self _
  obtain ⟨z, hz⟩ := (IsAlgClosed.splits _).mem_range_of_isRoot hf hroot
  exact ⟨z, hz.symm⟩

theorem eq_of_forall_dvd_root_sub {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [CharP O l] [PerfectRing O l]
    (c : O) [IsHausdorff (Ideal.span {c}) O] (v w : O)
    (h : ∀ n : ℕ, c ∣ ((frobeniusEquiv O l).symm)^[n] v - ((frobeniusEquiv O l).symm)^[n] w) : v = w := by
  have hp : ∀ (n : ℕ) (x : O), (((frobeniusEquiv O l).symm)^[n] x) ^ (l ^ n) = x := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ n ih => intro x; rw [Function.iterate_succ_apply, pow_succ, pow_mul, ih, frobeniusEquiv_symm_pow_p]
  rw [← sub_eq_zero]
  refine IsHausdorff.haus' (I := Ideal.span {c}) _ fun n => ?_
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  have h1 := pow_dvd_pow_of_dvd (h n) (l ^ n)
  rw [sub_pow_char_pow, hp, hp] at h1
  exact (pow_dvd_pow c (Nat.lt_pow_self (Fact.out : l.Prime).one_lt).le).trans h1

theorem exists_gal_of_teichmuller_congr : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (O : Type) [CommRing O] [IsDomain O] [ValuationRing O] [CharP O l] [PerfectRing O l] (ψ : OCb l →+* O), ψ bk.flat ≠ 0 → ¬ IsUnit (ψ bk.flat) → IsAdicComplete (Ideal.span {ψ bk.flat}) O → ∀ v : O, WittVector.map ψ (bk.ev bk.E) ∣ WittVector.teichmuller l v - WittVector.teichmuller l (ψ bk.flat) → ∃ g : ↥(GK K), v = ψ (Per.σF (g : GQ l) bk.flat) := by
  intro l _ K bk O _ _ _ _ _ ψ h0 hu hc v hv
  have hl : 0 < l := (Fact.out : l.Prime).pos
  obtain ⟨f, hf, hinj, hdom, hmod⟩ := GlobalTheory.T.exists_injective_map_integers_Cl_to_wittQuotient l K bk O ψ h0 hu hc
  obtain ⟨hprime, hπ⟩ := GlobalTheory.T.breuilKisin_prime_uniformizer_class l K bk
  obtain ⟨halg, hfix⟩ := GlobalTheory.T.untiltOfTiltRoot_flat_algebraic_and_galois_fix l K bk
  set π : ↥(OL K) := bk.str.symm (Ideal.Quotient.mk _ (X : bk.S)) with hπd
  have hft : ∀ y : OCb l, f y.untilt = Ideal.Quotient.mk _ (WittVector.teichmuller l (ψ y)) := fun y => by
    rw [← WittVector.fontaineTheta_teichmuller, ← WittVector.map_teichmuller]
    exact hf _
  let r : ℕ → WittVector l O ⧸ Ideal.span {WittVector.map ψ (bk.ev bk.E)} := fun n =>
    Ideal.Quotient.mk _ (WittVector.teichmuller l (((frobeniusEquiv O l).symm)^[n] v))
  have hr0 : r 0 = f bk.flat.untilt := by
    rw [hft]
    exact Ideal.Quotient.eq.2 (Ideal.mem_span_singleton.2 hv)
  have hrs : ∀ n, r (n + 1) ^ l = r n := fun n => by
    simp only [r]
    rw [← map_pow, ← map_pow, Function.iterate_succ_apply', frobeniusEquiv_symm_pow_p]
  have hrn : ∀ n, r n ^ (l ^ n) = f bk.flat.untilt := fun n => by
    induction n with
    | zero => rw [pow_zero, pow_one, hr0]
    | succ n ih => rw [pow_succ', pow_mul, hrs, ih]
  choose s hs using fun n => exists_OC_eq_of_pow_eq f (pow_pos hl n) _ _ (hrn n)
  have hss : ∀ n, s (n + 1) ^ l = s n := fun n => hinj (by rw [map_pow, hs, hs, hrs])
  have hsn : ∀ n, s n ^ (l ^ n) = bk.flat.untilt := fun n => hinj (by rw [map_pow, hs, hrn])
  have hπc : ((bk.flat.untilt : OC l) : ℂ_[l]) = (((π : ↥K.1) : Om l) : ℂ_[l]) := by
    rw [← hπ, coe_intToOC]
  have hcoe : Function.Injective (fun z : Om l => (z : ℂ_[l])) := (algebraMap (Om l) ℂ_[l]).injective
  have hcp : ∀ (z : Om l) (m : ℕ), ((z ^ m : Om l) : ℂ_[l]) = (z : ℂ_[l]) ^ m :=
    fun z m => map_pow (algebraMap (Om l) ℂ_[l]) z m
  choose z hz using fun n => exists_alg_eq_of_pow_eq (pow_pos hl n) ((π : ↥K.1) : Om l) (s n : ℂ_[l])
    (by rw [← hπc, ← hsn n, SubmonoidClass.coe_pow])
  choose y hy using halg
  have hts : ∀ n, GlobalTheory.MemLoc.rootT bk.flat (n + 1) ^ l = GlobalTheory.MemLoc.rootT bk.flat n := fun n => by
    rw [GlobalTheory.MemLoc.rootT, GlobalTheory.MemLoc.rootT, ← map_pow, Function.iterate_succ_apply', frobeniusEquiv_symm_pow_p]
  obtain ⟨g, hg⟩ := GlobalTheory.T.galois_transitive_on_prime_power_root_systems l K π hprime y z
    (hcoe (by
      change ((y 0 : Om l) : ℂ_[l]) = (((π : ↥K.1) : Om l) : ℂ_[l])
      rw [← hy, ← hπc]
      rfl))
    (hcoe (by
      change ((z 0 : Om l) : ℂ_[l]) = (((π : ↥K.1) : Om l) : ℂ_[l])
      rw [← hz, ← hπc, ← hsn 0, pow_zero, pow_one]))
    (fun n => hcoe (by
      change ((y (n + 1) ^ l : Om l) : ℂ_[l]) = ((y n : Om l) : ℂ_[l])
      rw [hcp, ← hy, ← hy, ← hts n, SubmonoidClass.coe_pow]))
    (fun n => hcoe (by
      change ((z (n + 1) ^ l : Om l) : ℂ_[l]) = ((z n : Om l) : ℂ_[l])
      rw [hcp, ← hz, ← hz, ← hss n, SubmonoidClass.coe_pow]))
  obtain ⟨w, hw⟩ := GlobalTheory.tilt_of_compatible_roots l s hss
  have hgw : Per.σF (g : GQ l) bk.flat = w := hfix _ _ fun n => Subtype.ext (by
    refine (GlobalTheory.RingIface.sigO_coe l (g : GQ l) (GlobalTheory.MemLoc.rootT bk.flat n)).trans ?_
    rw [hy, hw, hz, ← hg n]
    exact GlobalTheory.RingBasics.σC_coe _ _)
  refine ⟨g, ?_⟩
  rw [hgw]
  refine eq_of_forall_dvd_root_sub (l := l) (ψ bk.flat) v (ψ w) fun n => ?_
  have hψ : ∀ m, ψ (((frobeniusEquiv (OCb l) l).symm)^[m] w) = ((frobeniusEquiv O l).symm)^[m] (ψ w) := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih, RingHom.map_frobeniusEquiv_symm]
  have h1 := hft (((frobeniusEquiv (OCb l) l).symm)^[n] w)
  have h2 : f (s n) = Ideal.Quotient.mk _ (WittVector.teichmuller l (((frobeniusEquiv O l).symm)^[n] (ψ w))) := by
    rw [← hw n, ← hψ]
    exact h1
  have h3 := hmod (WittVector.teichmuller l (((frobeniusEquiv O l).symm)^[n] v) -
      WittVector.teichmuller l (((frobeniusEquiv O l).symm)^[n] (ψ w)))
    (by rw [map_sub, ← h2, hs, sub_self]; exact dvd_zero _)
  rw [← WittVector.constantCoeff_apply, map_sub, WittVector.constantCoeff_apply, WittVector.constantCoeff_apply,
    WittVector.teichmuller_coeff_zero, WittVector.teichmuller_coeff_zero] at h3
  exact (dvd_pow_self _ bk.deg_pos.ne').trans h3

end GlobalTheory.BSP
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsGrpPullbackGenericFibre
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR.QForm (QVal IsQ bOf)

noncomputable section

open scoped CategoryTheory.Obj

namespace GlobalTheory.GenericFibreUnif

theorem exists_isGrpPullback_genericFibre : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (χ : Sp R ⟶ Y.X) (t : SAB H (Sp R)) (m : SABMap t Y.t χ) (P : PELUnif I t) (z : Sp (FractionRing R) ⟶ Xo.XF c), z ≫ Y.j = jK R ≫ χ → letI := H.starRing; ∃ ψ : P.A.A.left ⟶ Y.oF.t.G.left, IsGrpPullback P.A.A Y.oF.t.G z ψ ∧ LBIso P.A.L (Y.oF.t.PP.L.pull ψ) ∧ (∀ a : 𝓞 E, (P.oA.act a).left ≫ ψ = ψ ≫ (Y.oF.t.act.act a).left) ∧ ψ ≫ Y.m.φ = P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK R) ≫ m.φ := by
  intro E _ _ _ H Dw l Xo c O _ β Y R _ _ I χ t m P z hz
  letI := H.starRing
  have := P.U.gen_hom
  have : IsMonHom P.U.gen.symm.hom := by show IsMonHom P.U.gen.inv; infer_instance
  set k : P.A.A.left ⟶ t.G.left := P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK R) with hk
  have gpG : IsGrpPullback P.A.A t.G (jK R) k :=
    ((isGrpPullback_of_iso P.U.gen.symm).comp (isGrpPullback_pullback t.G (jK R))).congr (Category.id_comp _) rfl
  have n₀ : IsGrpPullback P.A.A Y.t.G (jK R ≫ χ) (k ≫ m.φ) := gpG.comp m.cart
  have hw : (k ≫ m.φ) ≫ Y.t.G.hom = (P.A.A.hom ≫ z) ≫ (Y.jQ ≫ pullback.fst _ _) := by
    refine n₀.1.w.trans ?_
    rw [← hz, Category.assoc]; rfl
  let ψ : P.A.A.left ⟶ Y.oF.t.G.left := Y.m.cart.1.lift (k ≫ m.φ) (P.A.A.hom ≫ z) hw
  have hψ₁ : ψ ≫ Y.m.φ = k ≫ m.φ := Y.m.cart.1.lift_fst _ _ _
  have hψ₂ : ψ ≫ Y.oF.t.G.hom = P.A.A.hom ≫ z := Y.m.cart.1.lift_snd _ _ _
  have n : IsGrpPullback P.A.A Y.t.G (z ≫ (Y.jQ ≫ pullback.fst _ _)) (ψ ≫ Y.m.φ) :=
    n₀.congr hz.symm hψ₁.symm
  have cart : IsGrpPullback P.A.A Y.oF.t.G z ψ := Y.m.cart.cancel n hψ₂
  have actA : ∀ x, (P.oA.act x).left ≫ k = k ≫ (t.act.act x).left := by
    intro x
    have e : P.oA.act x ≫ P.U.gen.inv = P.U.gen.inv ≫ (Over.pullback (jK R)).map (t.act.act x) := by
      rw [Iso.comp_inv_eq, Category.assoc]
      exact ((Iso.inv_comp_eq _).2 (P.lin.ext x)).symm
    rw [hk, ← Category.assoc, ← Over.comp_left, e, Over.comp_left, Category.assoc]
    exact congrArg _ (pullback.lift_fst _ _ _)

  have hgi : P.U.gen.inv.left ≫ P.U.gen.hom.left = 𝟙 _ := by
    rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]
  have B₁ : LBIso (P.A.L.pull (𝟙 _)) (P.U.LG.L.pull k) :=
    LBIso.chartPull (chartPullSame P.A.L (fun _ => 𝟙 _) (fun _ => P.U.gen.hom.left) _ P.U.gen.inv.left
        (fun _ => hgi.symm))
      (chartPullSame P.U.LG.L (fun _ => k) (fun _ => pullback.fst t.G.hom (jK R)) _ P.U.gen.inv.left
        (fun _ => rfl)) P.U.ext
  have B₁' : LBIso P.A.L (t.PP.L.pull k) := by
    rw [← P.bundle]
    exact LBIso.chartPull (chartPullUnpull P.A.L (𝟙 _) rfl) (chartPullId _) B₁
  obtain ⟨w₂, -, g₂, -⟩ := rigIso_congr rfl m.cm m.lin rfl rfl
  have B₂ : LBIso (t.PP.L.pull k) (Y.t.PP.L.pull (ψ ≫ Y.m.φ)) :=
    LBIso.chartPull (chartPullPull t.PP.L k k rfl)
      (chartPullSame Y.t.PP.L (fun _ => ψ ≫ Y.m.φ) (fun _ => m.φ) _ k (fun _ => hψ₁.trans (Category.assoc _ _ _)))
      ⟨w₂, g₂⟩
  obtain ⟨w₃, -, g₃, -⟩ := rigIso_congr rfl Y.m.cm Y.m.lin rfl rfl
  have B₃ : LBIso (Y.oF.t.PP.L.pull ψ) (Y.t.PP.L.pull (ψ ≫ Y.m.φ)) :=
    LBIso.chartPull (chartPullPull Y.oF.t.PP.L ψ ψ rfl)
      (chartPullSame Y.t.PP.L (fun _ => ψ ≫ Y.m.φ) (fun _ => Y.m.φ) _ ψ (fun _ => rfl)) ⟨w₃, g₃⟩
  have BL : LBIso P.A.L (Y.oF.t.PP.L.pull ψ) :=
    LBIso.trans P.A.isLB (pull_isLB Y.t.PP.isLB _) (pull_isLB Y.oF.t.PP.isLB _)
      (LBIso.trans P.A.isLB (pull_isLB t.PP.isLB _) (pull_isLB Y.t.PP.isLB _) B₁' B₂) (LBIso.symm B₃)
  refine ⟨ψ, cart, BL, fun a => ?_, hψ₁.trans (Category.assoc _ _ _)⟩
  apply Y.m.cart.1.hom_ext
  · calc ((P.oA.act a).left ≫ ψ) ≫ Y.m.φ = (P.oA.act a).left ≫ k ≫ m.φ := by rw [Category.assoc, hψ₁]
      _ = k ≫ m.φ ≫ (Y.t.act.act a).left := by rw [← Category.assoc, actA, Category.assoc, m.act a]
      _ = (ψ ≫ (Y.oF.t.act.act a).left) ≫ Y.m.φ := by
        rw [Category.assoc ψ, Y.m.act a, ← Category.assoc ψ, hψ₁]; exact (Category.assoc _ _ _).symm
  · rw [Category.assoc, hψ₂, ← Category.assoc, Over.w (P.oA.act a), Category.assoc, Over.w (Y.oF.t.act.act a), hψ₂]

end GlobalTheory.GenericFibreUnif
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLPowIHatToHatSSubDvd
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.BK

open PowerSeries Filter Topology

section Bounded

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] (l : ℕ) [Fact l.Prime] [NormedAlgebra ℚ_[l] K] (e : ℕ) [NeZero e]

omit [IsUnitBall O K] in

theorem norm_tail_mul_rad_le {f : K⟦X⟧} {b : ℝ} (hb : 0 ≤ b)
    (hf : ∀ n, ‖coeff n f‖ * rad l (1 / e) ^ n ≤ b) (n : ℕ) :
    ‖tail l e f n‖ * rad l (1 / e) ^ n ≤ b := by
  have hρ := pow_pos (rad_pos l (1 / e)) n
  rw [← le_div_iff₀ hρ]
  refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (div_nonneg hb hρ.le) fun j => ?_
  rw [le_div_iff₀ hρ, norm_term_eq]
  exact hf _

theorem coeff_sub_E_mul_quotE_of_lt [CompleteSpace K] {f : K⟦X⟧} (hf : f ∈ Rpi O K l e) {n : ℕ}
    (hn : n < e) : coeff n (f - E K l e * quotE l e f) = tail l e f n := by
  rw [tail_rec l e hf n, map_sub, E, add_mul, map_add, coeff_X_pow_mul', if_neg (by omega),
    ← map_natCast (C : K →+* K⟦X⟧) l, coeff_C_mul, quotE, coeff_mk]
  ring

theorem norm_coeff_mul_rad_le_of_mem_S {f : K⟦X⟧} (hf : f ∈ S O K e) (n : ℕ) :
    ‖coeff n f‖ * rad l (1 / e) ^ n ≤ 1 := by
  refine le_trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)) (hf.1 n)
  refine le_trans ?_ (norm_pow_le_norm_factorial (K := K) l (n / e))
  rw [← rad_pow (K := K) l e, ← pow_mul]
  exact pow_le_pow_of_le_one (rad_nonneg _ _) (rad_le_one l (by positivity)) (Nat.mul_div_le n e)

theorem exists_bdd_div_E_pow [CompleteSpace K] (m : ℕ) {f : K⟦X⟧} (hf : f ∈ Rpi O K l e)
    {b : ℝ} (hb : 0 ≤ b) (hfb : ∀ n, ‖coeff n f‖ * rad l (1 / e) ^ n ≤ b) :
    ∃ g : K⟦X⟧, (∀ n, ‖coeff n g‖ ≤ b * ‖(l : K)‖⁻¹ ^ m) ∧
      ∃ h ∈ Rpi O K l e, f = g + E K l e ^ m * h := by
  induction m generalizing f b with
  | zero => exact ⟨0, fun n => by simpa using hb, f, hf, by simp⟩
  | succ m ih =>
    have hl0 : 0 < ‖(l : K)‖ := norm_pos_iff.2 (l_ne_zero l)
    have hl1 : ‖(l : K)‖ < 1 := norm_l_lt_one l
    have hρe : rad l (1 / e) ^ e = ‖(l : K)‖ := rad_pow l e
    have hρ0 : 0 < rad l (1 / e) := rad_pos l _
    have hρ1 : rad l (1 / e) ≤ 1 := rad_le_one l (by positivity)
    have htail := norm_tail_mul_rad_le l e hb hfb
    have hq : ∀ n, ‖coeff n (quotE l e f)‖ * rad l (1 / e) ^ n ≤ b * ‖(l : K)‖⁻¹ := fun n => by
      have := htail (n + e)
      rw [pow_add, hρe] at this
      rw [quotE, coeff_mk, le_mul_inv_iff₀ hl0]
      simpa [mul_assoc] using this
    obtain ⟨g1, hg1, h1, hh1, hq1⟩ :=
      ih (quotE_mem_Rpi l e hf) (mul_nonneg hb (inv_nonneg.2 hl0.le)) hq
    have hpow : ‖(l : K)‖⁻¹ ≤ ‖(l : K)‖⁻¹ ^ (m + 1) := by
      simpa using pow_le_pow_right₀ (one_le_inv₀ hl0 |>.2 hl1.le) (Nat.succ_le_succ (Nat.zero_le m))
    refine ⟨(f - E K l e * quotE l e f) + E K l e * g1, fun n => ?_, h1, hh1, ?_⟩
    · rw [map_add]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
      · rcases lt_or_ge n e with hn | hn
        · rw [coeff_sub_E_mul_quotE_of_lt l e hf hn]
          have h2 := htail n
          have h3 : ‖(l : K)‖ ≤ rad l (1 / e) ^ n := by
            rw [← hρe]; exact pow_le_pow_of_le_one hρ0.le hρ1 hn.le
          have h4 : ‖tail l e f n‖ ≤ b * ‖(l : K)‖⁻¹ := by
            rw [le_mul_inv_iff₀ hl0]
            exact (mul_le_mul_of_nonneg_left h3 (norm_nonneg _)).trans h2
          exact h4.trans (mul_le_mul_of_nonneg_left hpow hb)
        · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn
          rw [coeff_sub_E_mul_quotE l e hf, norm_zero]
          positivity
      · have hE : ∀ n, ‖coeff n (E K l e)‖ * (1 : ℝ) ≤ 1 := fun n => by
          simpa using (E_mem l e (A O K)) n
        have := norm_coeff_mul_le (w := fun _ => (1 : ℝ)) (fun _ => zero_le_one)
          (fun _ _ => by simp) (a := 1) (b := b * ‖(l : K)‖⁻¹ * ‖(l : K)‖⁻¹ ^ m) zero_le_one
          (by positivity) hE (g := g1) (fun n => by rw [mul_one]; exact hg1 n) n
        have e' : (1 : ℝ) * (b * ‖(l : K)‖⁻¹ * ‖(l : K)‖⁻¹ ^ m) = b * ‖(l : K)‖⁻¹ ^ (m + 1) := by
          ring
        rw [mul_one, e'] at this
        exact this
    · linear_combination E K l e * hq1

end Bounded

end GlobalTheory.BK

namespace GlobalTheory.BKReal

open PowerSeries GlobalTheory.BK

theorem exists_l_pow_iHat_toHatS_sub_dvd (l : ℕ) [Fact l.Prime] (e : ℕ) [NeZero e] (O K : Type)
    [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K]
    [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (ϖ : PiSys l e)
    [CompleteSpace K] (m : ℕ) (s : S O K e) :
    ∃ y : OA l O, ϖ.iAl O K (EIn l e _) ^ m ∣
      (l : OD l O) ^ m * ϖ.iHat O K (toHatS O K l e (algebraMap (S O K e) (invL l (S O K e)) s)) -
        toOD l O y := by
  obtain ⟨g, hg, h, hh, hs⟩ := exists_bdd_div_E_pow l e m (S_le_R l e s.2) zero_le_one
    (norm_coeff_mul_rad_le_of_mem_S l e s.2)
  have hl0 : ‖(l : K)‖ ≠ 0 := norm_ne_zero_iff.2 (GlobalTheory.BK.l_ne_zero (K := K) l)
  have hG : C ((l : K) ^ m) * g ∈ A O K := fun n => by
    rw [coeff_C_mul, norm_mul, norm_pow]
    calc _ ≤ ‖(l : K)‖ ^ m * (1 * ‖(l : K)‖⁻¹ ^ m) := by gcongr; exact hg n
      _ = 1 := by rw [one_mul, ← mul_pow, mul_inv_cancel₀ hl0, one_pow]
  have hH : C ((l : K) ^ m) * h ∈ Rpi O K l e := mul_mem (HasK.C_mem _) hh
  have key : (l : Rpi O K l e) ^ m * Subalgebra.inclusion (invL_S_le_Rpi l e)
      (algebraMap (S O K e) (invL l (S O K e)) s) =
      ⟨_, A_le_Rpi l e hG⟩ + EIn l e (Rpi O K l e) ^ m * ⟨_, hH⟩ := by
    apply Subtype.ext
    simp only [Subalgebra.coe_mul, Subalgebra.coe_add, Subalgebra.coe_pow, SubringClass.coe_natCast,
      Subalgebra.coe_inclusion, coe_algebraMap_away, coe_EIn, map_pow, map_natCast]
    rw [hs]
    ring
  have e1 : ϖ.iHat O K (toHat O K l e ⟨_, A_le_Rpi l e hG⟩) = toOD l O (ϖ.iA O K ⟨_, hG⟩) :=
    (congrArg (ϖ.iHat O K)
      (toHat_eq_ofAl l e (g := algebraMap (A O K) (invL l (A O K)) ⟨_, hG⟩) rfl)).trans
      (ϖ.iHat_ofA O K _)
  have e2 : ϖ.iHat O K (Ehat O K l e) = ϖ.iAl O K (EIn l e _) := ϖ.iHat_ofAl O K _
  have h1 : (l : OD l O) ^ m *
      ϖ.iHat O K (toHatS O K l e (algebraMap (S O K e) (invL l (S O K e)) s)) =
      ϖ.iHat O K (toHat O K l e ((l : Rpi O K l e) ^ m * Subalgebra.inclusion (invL_S_le_Rpi l e)
        (algebraMap (S O K e) (invL l (S O K e)) s))) := by
    simp only [map_mul, map_pow, map_natCast]
    rfl
  refine ⟨ϖ.iA O K ⟨_, hG⟩, ϖ.iHat O K (toHat O K l e ⟨_, hH⟩), ?_⟩
  rw [h1, key]
  rw [map_add (toHat O K l e), map_add (ϖ.iHat O K), map_mul (toHat O K l e), map_mul (ϖ.iHat O K),
    map_pow (toHat O K l e), map_pow (ϖ.iHat O K), toHat_E, e1, e2]
  ring

end GlobalTheory.BKReal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsMemSpanCornerSeparable
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.SpanRing

namespace GlobalTheory.SpanRing

theorem exists_mem_span_corner_separable {K Γ : Type} [Field K] [Infinite K] [Group Γ] {n t : ℕ}
    (σ : Γ →* Matrix (Fin n) (Fin n) K) (a : Matrix (Fin n) (Fin t) K)
    (b : Matrix (Fin t) (Fin n) K) (h : AbsIrrDistinct (matRep σ)) (hba : b * a = 1)
    (hab : a * b ∈ Submodule.span K (Set.range σ)) :
    ∃ m ∈ Submodule.span K (Set.range σ), (b * m * a).charpoly.Separable := by
  obtain ⟨ι, _, _, Vs, hs, hint, -, hspan, hdist⟩ := h
  have hstab : ∀ j, ∀ M ∈ Submodule.span K (Set.range σ), ∀ v ∈ Vs j, M.mulVec v ∈ Vs j := by
    intro j M hM
    induction hM using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, rfl⟩ := hx
      intro v hv
      exact hs j g v hv
    | zero => intro v _; simp
    | add x y _ _ hx hy =>
      intro v hv
      rw [Matrix.add_mulVec]
      exact (Vs j).add_mem (hx v hv) (hy v hv)
    | smul c x _ hx =>
      intro v hv
      rw [show (c • x).mulVec v = c • x.mulVec v by
        ext i; simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]]
      exact (Vs j).smul_mem c (hx v hv)
  obtain ⟨m, hm, hsep⟩ := GlobalTheory.T.exists_corner_separable_charpoly_of_isInternal ι Vs a b hint hba (fun j => hstab j _ hab)
  refine ⟨m, ?_, hsep⟩
  have hlin := GlobalTheory.T.span_representation_density_of_isInternal_constituents (matRep σ) ι Vs hs hint hspan hdist (Matrix.toLin' m)
    (fun j v hv => by simpa [Matrix.toLin'_apply] using hm j v hv)
  have hfun : (⇑(matRep σ)) = ⇑(Matrix.toLin' : Matrix (Fin n) (Fin n) K ≃ₗ[K] _) ∘ ⇑σ := rfl
  rw [hfun, Set.range_comp] at hlin
  have hle : Submodule.span K (⇑(Matrix.toLin' : Matrix (Fin n) (Fin n) K ≃ₗ[K] _) '' Set.range ⇑σ) ≤
      (Submodule.span K (Set.range σ)).map
        (Matrix.toLin' : Matrix (Fin n) (Fin n) K ≃ₗ[K] _).toLinearMap := by
    rw [Submodule.span_le]
    rintro _ ⟨M, hM, rfl⟩
    exact ⟨M, Submodule.subset_span hM, rfl⟩
  obtain ⟨y, hy, hye⟩ := hle hlin
  have hym : y = m := Matrix.toLin'.injective hye
  rwa [hym] at hy

end GlobalTheory.SpanRing
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPowMulNormLe
section
namespace GlobalTheory.NatCastNormLtOne

theorem norm_natCast_lt_one {l : ℕ} [Fact (Nat.Prime l)] {K : Type} [NormedField K]
    [NormedAlgebra ℚ_[l] K] : ‖(l : K)‖ < 1 := by
  have h : (l : K) = algebraMap ℚ_[l] K (l : ℚ_[l]) := by simp
  rw [h, norm_algebraMap']
  exact Padic.norm_p_lt_one

theorem exists_pow_mul_norm_le {K : Type} [NormedField K] {x : K} (hx : ‖x‖ < 1) (a : K) :
    ∃ n : ℕ, ‖x ^ n * a‖ ≤ 1 := by
  have h : Filter.Tendsto (fun n : ℕ => ‖x‖ ^ n * ‖a‖) Filter.atTop (nhds (0 * ‖a‖)) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg x) hx).mul_const _
  rw [zero_mul] at h
  obtain ⟨n, hn⟩ := (h.eventually (gt_mem_nhds (zero_lt_one' ℝ))).exists
  exact ⟨n, by rw [norm_mul, norm_pow]; exact hn.le⟩

theorem exists_pow_smul_mem {l : ℕ} [hl : Fact (Nat.Prime l)] {O K : Type} [CommRing O]
    [NormedField K] [Algebra O K] [GlobalTheory.BK.IsUnitBall O K] [NormedAlgebra ℚ_[l] K]
    {V : Type} [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V]
    (T : Submodule O V) (hT : Submodule.span K (T : Set V) = ⊤) (v : V) :
    ∃ n : ℕ, (l : K) ^ n • v ∈ T := by
  have hpow : ∀ (k : ℕ) (w : V), w ∈ T → (l : K) ^ k • w ∈ T := by
    intro k w hw
    have h : (l : K) ^ k = algebraMap O K ((l : O) ^ k) := by simp
    rw [h, algebraMap_smul]
    exact T.smul_mem _ hw
  have hv : v ∈ Submodule.span K (T : Set V) := by rw [hT]; trivial
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨0, by simpa using hx⟩
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨n, hn⟩ := hx
    obtain ⟨m, hm⟩ := hy
    refine ⟨n + m, ?_⟩
    rw [smul_add]
    refine T.add_mem ?_ ?_
    · rw [add_comm, pow_add, mul_smul]; exact hpow _ _ hn
    · rw [pow_add, mul_smul]; exact hpow _ _ hm
  | smul a x _ hx =>
    obtain ⟨n, hn⟩ := hx
    obtain ⟨m, hm⟩ := exists_pow_mul_norm_le (norm_natCast_lt_one (l := l) (K := K)) a
    obtain ⟨b, hb⟩ := (GlobalTheory.BK.IsUnitBall.mem_range_iff (O := O) ((l : K) ^ m * a)).2 hm
    refine ⟨m + n, ?_⟩
    have h : (l : K) ^ (m + n) • a • x = b • ((l : K) ^ n • x) := by
      rw [← algebraMap_smul K b, hb, smul_smul, smul_smul]
      congr 1
      ring
    rw [h]
    exact T.smul_mem _ hn

theorem main : ∀ {l : ℕ} [hl : Fact (Nat.Prime l)] {O K : Type} [inst : CommRing O]
    [inst_1 : NormedField K] [inst_2 : Algebra O K] [GlobalTheory.BK.IsUnitBall O K]
    [inst_4 : NormedAlgebra ℚ_[l] K] {G : Type} [inst_5 : Group G] [inst_6 : TopologicalSpace G]
    (T : Formalism.BasicNotions.LocLat G ℚ_[l] K O) (v : Formalism.BasicNotions.LocLat.V T),
    ∃ (n : ℕ), (↑l : K) ^ n • v ∈ Formalism.WeaklyAdmissibleFiltrations.Lattice.T (Formalism.BasicNotions.LocLat.L T) := by
  intro l _ O K _ _ _ _ _ G _ _ T v
  exact exists_pow_smul_mem T.L.T T.L.span v

end GlobalTheory.NatCastNormLtOne
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUniformiserEisensteinNotInXPowStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_uniformiser_eisenstein_not_in_X_pow : ∀ (l : ℕ) [Fact l.Prime] (a : ℕ) [NeZero a] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra (Wq l a) O] [Module.Finite (Wq l a) O], Function.Injective (algebraMap (Wq l a) O) → (∀ x : O, ∃ c : Wq l a, ¬ IsUnit (x - algebraMap (Wq l a) O c)) → ∃ (π : O) (Ep : Polynomial (Wq l a)), Irreducible π ∧ (Ep.Monic ∧ 0 < Ep.natDegree ∧ (∀ i < Ep.natDegree, (l : Wq l a) ∣ Ep.coeff i) ∧ (∃ w : (Wq l a)ˣ, Ep.coeff 0 = (l : Wq l a) * w)) ∧ (∃ i, ¬ l ∣ i ∧ Ep.coeff i ≠ 0) ∧ Polynomial.aeval π Ep = 0 ∧ (∀ x : O, ∃ f : Polynomial (Wq l a), Polynomial.aeval π f = x) ∧ ∀ f : Polynomial (Wq l a), Polynomial.aeval π f = 0 → Ep ∣ f := by
  first | exact @GlobalTheory.EisShift.exists_uniformiser | exact GlobalTheory.EisShift.exists_uniformiser | (intros; apply GlobalTheory.EisShift.exists_uniformiser <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankFiniteLeExponentialCocyclesStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.HyodoDef GlobalTheory.Pst TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_finite_le_exponential_cocycles : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] [ContinuousAdd V] [ContinuousConstSMul ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V), (∀ v, Continuous fun g => ρ g v) → IsDR (P.PD K) ρ → finrank ℚ_[l] ↥(finiteCocycles (P.PD K) ρ) ≤ finrank ℚ_[l] ↥(crystallineCocycles (P.PD K) ρ) + finrank ℚ_[l] ↥(Dcris (P.PD K) ρ ⊓ LinearMap.ker (φVB (P.PD K) (LL := ℚ_[l]) (V := V) - LinearMap.id)) := by
  first | exact @GlobalTheory.HyodoFE.finrank_finite_le_exponential_add | exact GlobalTheory.HyodoFE.finrank_finite_le_exponential_add | (intros; apply GlobalTheory.HyodoFE.finrank_finite_le_exponential_add <;> assumption)
end

