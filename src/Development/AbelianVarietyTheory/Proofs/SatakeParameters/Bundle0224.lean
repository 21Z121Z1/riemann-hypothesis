import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAdelicUnitaryTrivialOutsideSplitPlaceLocEq
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0070
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0001
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0197
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0125
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinrankLetterHomComp
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CharpolyWeilDelignePotSemistableEnlargeCoefficie
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0606
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0206
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0191
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0142
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineFormalismOfRegular
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0205
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0162
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0189
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0002

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaTrilinearFormLocalGroupInvariant
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [local instance] GlobalTheory.NPin.ThetaMod.acg GlobalTheory.NPin.ThetaMod.mod
namespace GlobalTheory.ThetaLocInv

theorem thetaRead_inv : ∀ (D : D7) (M : MtFam D) (i : D.nd.Loc) (rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r) (X : RowMod D rep (D.nd.j i)) (μ η : HChar D.host.E) (Θ : ThetaMod D M i X μ η) (s : SplitPlace D.host.E) (μw ηw : (s.w.adicCompletion D.host.E)ˣ →* ℂˣ) (ι : SB (Matrix (Fin D.R.nV) (Fin D.R.r) (s.w.adicCompletion D.host.E)) →ₗ[ℂ] Θ.Ω) (c : s.v.adicCompletion (maximalRealSubfield D.host.E) ≃+* s.w.adicCompletion D.host.E), (∀ (h : GAf D.host.E D.R.nV) (g : GAf D.host.E D.R.r), TrivOutside {s.v} h → TrivOutside {s.v} g → ∀ Φ Φ' : SB (Matrix (Fin D.R.nV) (Fin D.R.r) (s.w.adicCompletion D.host.E)), (Φ' : Matrix (Fin D.R.nV) (Fin D.R.r) (s.w.adicCompletion D.host.E) → ℂ) = om μw (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.r g)) (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.nV h)) Φ → Θ.ω (h, g) (ι Φ) = ((ηw (Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.nV h))) : ℂˣ) : ℂ) • ι Φ') → ∀ (Wl Vl : Type) [AddCommGroup Wl] [Module ℂ Wl] [AddCommGroup Vl] [Module ℂ Vl] (πl : Representation ℂ (GL (Fin D.R.nV) (s.w.adicCompletion D.host.E)) Wl) (σl : Representation ℂ (GL (Fin D.R.r) (s.w.adicCompletion D.host.E)) Vl) (T' : Wl →ₗ[ℂ] ↥(NG.AFall D.host.E D.R.nV (M.loc i).wt.ρ)), (∀ x : GAf D.host.E D.R.nV, TrivOutside {s.v} x → ∀ a, ((T' (πl (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.nV x)) a) : ↥(NG.AFall D.host.E D.R.nV (M.loc i).wt.ρ)) : GAf D.host.E D.R.nV → (M.loc i).wt.W) = NG.rt D.host.E D.R.nV x (T' a : GAf D.host.E D.R.nV → (M.loc i).wt.W)) → ∀ (T'' : Vl →ₗ[ℂ] ↥X.C), (∀ x : GAf D.host.E D.R.r, TrivOutside {s.v} x → ∀ a, ((T'' (σl (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.r x)) a) : ↥X.C) : X.A) = X.ρ x (T'' a)) → ∀ (g : GL (Fin D.R.r) (s.w.adicCompletion D.host.E)) (h : GL (Fin D.R.nV) (s.w.adicCompletion D.host.E)) (Φ Φ' : SB (Matrix (Fin D.R.nV) (Fin D.R.r) (s.w.adicCompletion D.host.E))), (Φ' : Matrix (Fin D.R.nV) (Fin D.R.r) (s.w.adicCompletion D.host.E) → ℂ) = om μw g h Φ → ∀ a c', Θ.Λ (ι Φ') (T' (twist πl (detChar (Fin D.R.nV) ηw) h a)) (T'' (σl g c')) = Θ.Λ (ι Φ) (T' a) (T'' c') := by
  intro D M i rep X μ η Θ s μw ηw ι c hι Wl Vl _ _ _ _ πl σl T' hT' T'' hT'' g h Φ Φ' hΦ' a c'
  obtain ⟨xh, hxh, exh⟩ := GlobalTheory.SplitLift.exists_trivOutside_loc_eq D.R.nV s
    (Matrix.GeneralLinearGroup.map c.symm.toRingHom h)
  obtain ⟨xg, hxg, exg⟩ := GlobalTheory.SplitLift.exists_trivOutside_loc_eq D.R.r s
    (Matrix.GeneralLinearGroup.map c.symm.toRingHom g)
  have back : ∀ (n : ℕ) (A : GL (Fin n) (s.w.adicCompletion D.host.E)),
      Matrix.GeneralLinearGroup.map c.toRingHom (Matrix.GeneralLinearGroup.map c.symm.toRingHom A) = A := by
    intro n A
    ext k l
    simp
  have eh : Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.nV xh) = h := by rw [exh, back]
  have eg : Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.r xg) = g := by rw [exg, back]
  have hω := hι xh xg hxh hxg Φ Φ' (by rw [eh, eg]; exact hΦ')
  have key := Θ.inv xh xg (ι Φ) (T' a) (T' (πl h a)) (T'' c') (T'' (σl g c'))
    (by rw [← hT' xh hxh a, eh]) (by rw [← hT'' xg hxg c', eg])
  rw [hω, eh] at key
  rw [twist_apply, detChar_apply, map_smul, LinearMap.map_smul, LinearMap.smul_apply]
  rw [LinearMap.map_smul, LinearMap.smul_apply, LinearMap.smul_apply] at key
  simpa using key

end GlobalTheory.ThetaLocInv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ToAStRep
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Formalism.BasicNotions.Loc GlobalTheory.Pst GlobalTheory.WeilDeligne
open scoped TensorProduct
open GlobalTheory.Pst.TwistLetters
noncomputable section

open Module

namespace GlobalTheory.Pst.UnitLetter

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) (L : FinExt l)

def toA : ((Fin 1 → ↥L.1) ⊗[ℚ_[l]] Bst P) ≃ₗ[ℚ_[l]] Bst P ⊗[ℚ_[l]] ↥L.1 :=
  (TensorProduct.congr (LinearEquiv.funUnique (Fin 1) ℚ_[l] ↥L.1) (LinearEquiv.refl ℚ_[l] (Bst P))).trans
    (TensorProduct.comm ℚ_[l] ↥L.1 (Bst P))

@[simp] theorem toA_tmul (v : Fin 1 → ↥L.1) (b : Bst P) : toA P L (v ⊗ₜ b) = b ⊗ₜ v 0 := rfl

variable {P L}

theorem toA_mulB (y' y : (Fin 1 → ↥L.1) ⊗[ℚ_[l]] Bst P) :
    toA P L (GlobalTheory.Pst.TwistLetters.mulB P (Fin 1 → ↥L.1) y' y) = toA P L y' * toA P L y := by
  induction y' using TensorProduct.induction_on with
  | zero => simp
  | tmul v' b' =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul v b =>
      rw [GlobalTheory.Pst.TwistLetters.mulB_tmul, toA_tmul, toA_tmul, toA_tmul, Algebra.TensorProduct.tmul_mul_tmul]
      simp
    | add x x' hx hx' => simp only [map_add, mul_add, hx, hx']
  | add y y' hy hy' => simp only [map_add, LinearMap.add_apply, add_mul, hy, hy']

theorem toA_mulV (c : ↥(MaximalUnramifiedExtension l)) (y : (Fin 1 → ↥L.1) ⊗[ℚ_[l]] Bst P) :
    toA P L (mulV P ↥L.1 (Fin 1 → ↥L.1) c y) = algebraMap ↥(MaximalUnramifiedExtension l) (Bst P) c • toA P L y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul v b =>
    rw [mulV_tmul, toA_tmul, toA_tmul, TensorProduct.smul_tmul', smul_eq_mul]
  | add x x' hx hx' => simp only [map_add, smul_add, hx, hx']

theorem toA_stRep {K : FinExt l} (ρm : Representation ↥L.1 ↥(GK K) (Fin 1 → ↥L.1)) (χ : ↥(GK K) → ↥L.1)
    (hm : ∀ g v, ρm g v = χ g • v) (g : ↥(GK K)) (y : (Fin 1 → ↥L.1) ⊗[ℚ_[l]] Bst P) :
    toA P L (stRep P ρm g y) =
      Algebra.TensorProduct.map (actSt P (g : GQ l)) (AlgHom.id ℚ_[l] ↥L.1) (toA P L y) *
        ((1 : Bst P) ⊗ₜ[ℚ_[l]] χ g) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul v b =>
    rw [stRep_tmul, toA_tmul, toA_tmul, hm, Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.tmul_mul_tmul]
    simp [mul_comm]
  | add x x' hx hx' => simp only [map_add, add_mul, hx, hx']

end GlobalTheory.Pst.UnitLetter
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeightCocharacterEqOfGoodPlaces
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Hk3.LabDet

theorem adjoin_common {M : Type} [AddCommGroup M] [Module ℂ M] (s : Set (Module.End ℂ M)) (u u' : M)
    (h : ∀ x ∈ s, ∃ l : ℂ, x u = l • u ∧ x u' = l • u') :
    ∀ a ∈ Algebra.adjoin ℂ s, ∃ l : ℂ, a u = l • u ∧ a u' = l • u' := by
  first
  | exact @_root_.GlobalTheory.CommonEigenvalueAdjoin.exists_common_eigenvalue_of_mem_adjoin
  | exact _root_.GlobalTheory.CommonEigenvalueAdjoin.exists_common_eigenvalue_of_mem_adjoin
  | (apply _root_.GlobalTheory.CommonEigenvalueAdjoin.exists_common_eigenvalue_of_mem_adjoin <;> assumption)
  | (intros; apply _root_.GlobalTheory.CommonEigenvalueAdjoin.exists_common_eigenvalue_of_mem_adjoin <;> assumption)
  | (intros; apply @_root_.GlobalTheory.CommonEigenvalueAdjoin.exists_common_eigenvalue_of_mem_adjoin <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.CommonEigenvalueAdjoin.exists_common_eigenvalue_of_mem_adjoin ..)

variable {D : D7}

theorem opOf_single {V : HSp D} {M : Type} [AddCommGroup M] [Module ℂ M] (π : GA D V →* Module.End ℂ M) (P : Pl D.host.E)
    (d : List ℤ) : opOf π P (Finsupp.single d 1) = ∑ γ ∈ rep V P d, π γ := by
  unfold opOf
  rw [Finsupp.sum_single_index (by simp), one_smul]

theorem opOf_single_of_not {V : HSp D} {M : Type} [AddCommGroup M] [Module ℂ M] (π : GA D V →* Module.End ℂ M) (P : Pl D.host.E)
    (d : List ℤ) (h : ¬ IsLab V P d) : opOf π P (Finsupp.single d 1) = 0 := by
  rw [opOf_single]
  unfold rep
  rw [dif_neg h, Finset.sum_empty]

theorem sphOp_rep {V : HSp D} {P : Pl D.host.E} {d : List ℤ} (h : IsLab V P d) : SphOp V P d (rep V P d) := by
  unfold rep
  rw [dif_pos h]
  exact h.choose_spec

theorem eq_of_split {V : HSp D} {M : Type} [AddCommGroup M] [Module ℂ M] (π : GA D V →* Module.End ℂ M) (P : Pl D.host.E)
    (hP : conjPl P ≠ P) (u u' : M) (hu : u ≠ 0) (hu' : u' ≠ 0) (fu : ∀ k ∈ hyp V P, π k u = u) (fu' : ∀ k ∈ hyp V P, π k u' = u')
    (a a' b b' : List ℤ → ℂ)
    (ha : ∀ d, IsLab V P d → opOf π P (Finsupp.single d 1) u = a d • u)
    (ha' : ∀ d, IsLab V P d → opOf π P (Finsupp.single d 1) u' = a' d • u')
    (hb : ∀ d, IsLab V (conjPl P) d → opOf π (conjPl P) (Finsupp.single d 1) u = b d • u)
    (hb' : ∀ d, IsLab V (conjPl P) d → opOf π (conjPl P) (Finsupp.single d 1) u' = b' d • u')
    (ea : ∀ k, k ≤ V.rank → a (splitLab V.rank k) = a' (splitLab V.rank k))
    (eb : ∀ k, k ≤ V.rank → b (splitLab V.rank k) = b' (splitLab V.rank k)) :
    ∀ d, IsLab V P d → a d = a' d := by
  intro d hd
  obtain ⟨x, hx, hxe⟩ := GlobalTheory.T.exists_adjoin_splitHeckeGenerators_duals_spherical V P hP M π d
  obtain ⟨l, h1, h2⟩ := adjoin_common _ u u' (by
    rintro y ⟨k, hk, rfl | rfl⟩
    · by_cases hl : IsLab V P (splitLab V.rank k)
      · exact ⟨_, ha _ hl, by rw [ha' _ hl, ea k hk]⟩
      · exact ⟨0, by simp [opOf_single_of_not π P _ hl], by simp [opOf_single_of_not π P _ hl]⟩
    · have hc := (GlobalTheory.T.sphericalHecke_conjPlace_eq_dualLabel V P).2.2 (Finsupp.single (splitLab V.rank k) 1) M π
      have hd : dualC (Finsupp.single (splitLab V.rank k) 1) = Finsupp.single (dualLab (splitLab V.rank k)) 1 := by
        unfold dualC
        rw [Finsupp.mapDomain_single]
      rw [hd] at hc
      rw [← hc u fu, ← hc u' fu']
      by_cases hl : IsLab V (conjPl P) (splitLab V.rank k)
      · exact ⟨_, hb _ hl, by rw [hb' _ hl, eb k hk]⟩
      · exact ⟨0, by simp [opOf_single_of_not π _ _ hl], by simp [opOf_single_of_not π _ _ hl]⟩) x hx
  rw [hxe u fu, ha d hd] at h1
  rw [hxe u' fu', ha' d hd] at h2
  rw [smul_left_injective ℂ hu h1, smul_left_injective ℂ hu' h2]

def rLin (V : HSp D) (g : GA D V) : (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ) where
  toFun F := fun h => F (h * g)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def rRep {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) : GA D V →* Module.End ℂ (MMap M) where
  toFun g := postOn M (rLin V g)
  map_one' := by
    ext U v h
    show U v (h * 1) = U v h
    rw [mul_one]
  map_mul' g g' := by
    ext U v h
    show U v (h * (g * g')) = U v (h * g * g')
    rw [mul_assoc]

theorem rRep_apply {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (g : GA D V) (U : MMap M) (v : M.Vec) (h : GA D V) :
    rRep M g U v h = U v (h * g) := rfl

theorem sum_rRep {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (B : Finset (GA D V)) :
    ∑ γ ∈ B, rRep M γ = heckeOn M B := by
  ext U v h
  rw [LinearMap.sum_apply, MultilinearMap.sum_apply, Finset.sum_apply]
  rfl

theorem mult_lev {V : HSp D} {S : D.what₂.Tau → SPar} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
    (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ) (U : MMap M) (hU : U ∈ Mult θ M J χ) (k : GA D V) (hk : k ∈ J)
    (h1 : χ k = 1) : rRep M k U = U := by
  induction hU using Submodule.span_induction with
  | mem x hx =>
    ext v h
    rw [rRep_apply, hx.lev v k hk h, h1, one_mul]
  | zero => exact map_zero _
  | add x y _ _ hx hy => rw [map_add, hx, hy]
  | smul a x _ hx => rw [map_smul, hx]

theorem mem_partFull {V : HSp D} {S : D.what₂.Tau → SPar} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
    (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ) (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F)))
    (c : Pl D.host.E → List ℤ → ℂ) (U : MMap M) :
    U ∈ partFull θ M J χ Sb c ↔ U ∈ Mult θ M J χ ∧ ∀ P d B, Hecke₂ V J χ Sb P d B → heckeOn M B U = c P d • U := by
  unfold partFull
  simp only [Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.id_apply, sub_eq_zero]

theorem part_eq_of_labels : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Core R F → ∀ SF, IsSF R SF → ∀ i (c c' : Pl D.host.E → List ℤ → ℂ), Wcc R SF i c ≠ ⊥ → Wcc R SF i c' ≠ ⊥ → (∀ P, Good R A.μ0 P → conjPl P ≠ P → ∀ k, k ≤ (Wc D i).rank → c P (splitLab (Wc D i).rank k) = c' P (splitLab (Wc D i).rank k)) → (∀ P d, Good R A.μ0 P → conjPl P = P → IsLab (Wc D i) P d → c P d = c' P d) → Wcc R SF i c = Wcc R SF i c' := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hC SF hSF i c c' hc hc' hs hi
  obtain ⟨hQ, hgood, hoff, -⟩ := GlobalTheory.T.theta_lift_levels_good_primes_properties R F hC.lev
  obtain ⟨n, hβ⟩ := hC.lev.βW i
  have hlev := fun (P : Pl D.host.E) (hP : Good R A.μ0 P) =>
    GlobalTheory.T.level_operators_at_prime_off_level_datum (Wc D i) (R.βW i) (R.ΛW i) (1 ^ n) (R.datWp i R.triv) hβ P
      (by rw [one_pow, Nat.cast_one]; exact (Ideal.ne_top_iff_one _).1 P.isPrime.ne_top)
      (by
        intro PP hPP
        refine hP PP (hPP.imp id ?_)
        intro h
        exact absurd h (Finset.notMem_empty _))
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hc
  obtain ⟨x', hx', hx0'⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hc'
  have inj : Function.Injective (R.HW i (sg0 D A)).e := (hC.models.HW i (sg0 D A)).1
  have hu : (R.HW i (sg0 D A)).e x ≠ 0 := fun h => hx0 (inj (by rw [h, map_zero]))
  have hu' : (R.HW i (sg0 D A)).e x' ≠ 0 := fun h => hx0' (inj (by rw [h, map_zero]))
  have hp := (mem_partFull _ _ _ _ _ _ _).1 (Submodule.mem_inf.1 (Submodule.mem_comap.1 hx)).2
  have hp' := (mem_partFull _ _ _ _ _ _ _).1 (Submodule.mem_inf.1 (Submodule.mem_comap.1 hx')).2
  have key : ∀ P, Good R A.μ0 P → ∀ d, IsLab (Wc D i) P d → c P d = c' P d := by
    intro P hP
    by_cases hcP : conjPl P = P
    · exact fun d hd => hi P d hP hcP hd
    · have hP' : Good R A.μ0 (conjPl P) := (hgood _ P hP).2.1
      have hcc : conjPl (conjPl P) = P := ValuationRepresentative.conjPl_conjPl P
      refine eq_of_split (rRep (R.MW i (sg0 D A))) P hcP _ _ hu hu' ?_ ?_ (c P) (c' P) (c (conjPl P)) (c' (conjPl P)) ?_ ?_ ?_ ?_
        (hs P hP hcP) (hs _ hP' (by rw [hcc]; exact fun h => hcP h.symm))
      · exact fun k hk => mult_lev _ _ _ _ _ hp.1 k ((hlev P hP).1 k hk).1 ((hlev P hP).1 k hk).2
      · exact fun k hk => mult_lev _ _ _ _ _ hp'.1 k ((hlev P hP).1 k hk).1 ((hlev P hP).1 k hk).2
      · intro d hd
        rw [opOf_single, sum_rRep]
        exact hp.2 _ _ _ (((hlev P hP).2.1 SF d _).2 ⟨(hoff SF hSF P).2 hP, sphOp_rep hd⟩)
      · intro d hd
        rw [opOf_single, sum_rRep]
        exact hp'.2 _ _ _ (((hlev P hP).2.1 SF d _).2 ⟨(hoff SF hSF P).2 hP, sphOp_rep hd⟩)
      · intro d hd
        rw [opOf_single, sum_rRep]
        exact hp.2 _ _ _ (((hlev _ hP').2.1 SF d _).2 ⟨(hoff SF hSF _).2 hP', sphOp_rep hd⟩)
      · intro d hd
        rw [opOf_single, sum_rRep]
        exact hp'.2 _ _ _ (((hlev _ hP').2.1 SF d _).2 ⟨(hoff SF hSF _).2 hP', sphOp_rep hd⟩)
  have key2 : ∀ P d B, Hecke₂ (Wc D i) (levS _ (R.βW i) (R.datWp i R.triv)) (levChi _ (R.βW i) (R.datWp i R.triv)) SF P d B →
      c P d = c' P d := by
    intro P d B hB
    have hP : Good R A.μ0 P := by
      obtain ⟨_, _, _, _, ho, _⟩ := hB
      exact (hoff SF hSF P).1 ho
    exact key P hP d ⟨B, (((hlev P hP).2.1 SF d B).1 hB).2⟩
  unfold Wcc
  congr 2
  ext U
  rw [mem_partFull, mem_partFull]
  refine and_congr_right fun _ => forall_congr' fun P => forall_congr' fun d => forall_congr' fun B => imp_congr_right fun hB => ?_
  rw [key2 P d B hB]

end GlobalTheory.Hk3.LabDet

end
end

