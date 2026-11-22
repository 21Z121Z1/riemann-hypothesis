import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0270
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0290
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousKapSymm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0284
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StdLvPr
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0285
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsClassSumPairingFormsLat
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0288
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0281
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0279
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0158
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartWiden
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValLtOfRedM
import Formalism.LocalToGlobal.HermitianForms.Bundle0006
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0291
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsSplittingCharacterSelf
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MoveDownLevelFunctionalEq
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.DnFv

open GlobalTheory.LvT.Pts GlobalTheory.Mem.Col2.LvProj
open Formalism.HermitianLatticesTheory (localization₂ dual)

theorem dual_map_smul {F V : Type} {iF : CommSemiring F} {iV : AddCommMonoid V} {iM : Module F V} (φ : Module.Dual F V) (a : F) (y : V) :
    φ (a • y) = a * φ y := by
  rw [map_smul, smul_eq_mul]

section TD

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] {n : ℕ} {S : GStep E K n}
  {ST : Finset (HeightOneSpectrum (𝓞 E))} {A : TDat S ST} {T : ℕ}

theorem dn_extF_ok (ht : A.Tied T) (P : ST) (hM : MoveHyp ST ∅ P) (c : S.Cl)
    {g : Module.Dual (Res P.1) (A.lk P c)} (hg : g ≠ 0) :
    ((A.deco c.1 (S.rep c)).dn P (TDat.extF (A.dnN c.1 (S.rep c) P) P.1 g)).Ok := by
  have hN := ht.dnN_eq c.1 (S.rep c) P
  refine (ht.ok c.1 (S.rep c)).dn P hM ?_ ?_ ?_ ?_
  · intro x hx y hy
    rw [← hN] at hx hy
    rw [extF_of_mem g hx, extF_of_mem g hy, extF_of_mem g ((localization₂ _ _).add_mem hx hy), redL_add hx hy, map_add]
  · intro r x hx
    rw [← hN] at hx
    rw [extF_of_mem g hx, extF_of_mem g ((localization₂ _ _).smul_mem r hx), redL_osmul r hx, map_smul]
    rfl
  · intro x hx
    rw [← hN] at hx
    exact extF_of_notMem g hx
  · obtain ⟨z, hz⟩ : ∃ z, g z ≠ 0 := by
      by_contra H
      push Not at H
      exact hg (LinearMap.ext H)
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    refine ⟨x.1, hN ▸ x.2, ?_⟩
    rw [extF_of_mem g (le_locP _ _ x.2), redL_coe]
    exact hz

theorem N_dnPt (ht : A.Tied T) (P : ST) (hM : MoveHyp ST ∅ P) (c : S.Cl)
    {g : Module.Dual (Res P.1) (A.lk P c)} (hg : g ≠ 0) :
    A.N c.1 (A.dnPt P c g) = A.dnN c.1 (S.rep c) P := by
  have h := congrArg Deco.N (ht.dn_deco c.1 (S.rep c) P _ (dn_extF_ok ht P hM c hg))
  exact h.trans (ht.dnN_eq c.1 (S.rep c) P).symm

theorem f_dnPt (ht : A.Tied T) (P : ST) (hM : MoveHyp ST ∅ P) (c : S.Cl)
    {g : Module.Dual (Res P.1) (A.lk P c)} (hg : g ≠ 0) :
    A.f c.1 (A.dnPt P c g) P = TDat.extF (A.dnN c.1 (S.rep c) P) P.1 g := by
  classical
  have h := congrArg (fun d => Deco.f d P) (ht.dn_deco c.1 (S.rep c) P _ (dn_extF_ok ht P hM c hg))
  refine h.trans ?_
  simp [Deco.dn]

theorem fv_dn (ho : A.Ok T) (ht : A.Tied T) (hl : A.Laws T) (P : ST) (hM : MoveHyp ST ∅ P) (c : S.Cl)
    {g : Module.Dual (Res P.1) (A.lk P c)} (hg : g ≠ 0) {x : Fin n → E} {s : 𝓞 E} {G : Matrix (Fin n) (Fin n) E}
    (hG : G = (S.gam c.1 (S.mv c.1 (A.dnPt P c g)) : Matrix (Fin n) (Fin n) E))
    (hsx : s • x ∈ A.N (S.cl c.1 (A.dnPt P c g)).1 (S.rep (S.cl c.1 (A.dnPt P c g)))) :
    ∃ h : s • (G *ᵥ x) ∈ A.dnN c.1 (S.rep c) P,
      A.fv P (S.cl c.1 (A.dnPt P c g)) (Submodule.Quotient.mk ⟨_, hsx⟩) = g (Submodule.Quotient.mk ⟨_, h⟩) := by
  subst hG
  have hms : S.mv c.1 (A.dnPt P c g) • S.rep (S.cl c.1 (A.dnPt P c g)) = A.dnPt P c g := S.mv_smul c.1 _
  have e : (S.gam c.1 (S.mv c.1 (A.dnPt P c g)) : Matrix (Fin n) (Fin n) E) *ᵥ (s • x) =
      s • ((S.gam c.1 (S.mv c.1 (A.dnPt P c g)) : Matrix (Fin n) (Fin n) E) *ᵥ x) := by
    rw [← algebraMap_smul E s, ← algebraMap_smul E s, Matrix.mulVec_smul]
  have h1 := (ho.N_act c.1 (S.mv c.1 (A.dnPt P c g)) (S.rep (S.cl c.1 (A.dnPt P c g))) (s • x)).2 hsx
  rw [hms, N_dnPt ht P hM c hg, e] at h1
  refine ⟨h1, ?_⟩
  have h3 := ho.f_act c.1 (S.mv c.1 (A.dnPt P c g)) (S.rep (S.cl c.1 (A.dnPt P c g))) P (s • x)
  have h4 : redL (A.dnN c.1 (S.rep c) P) P.1 (s • ((S.gam c.1 (S.mv c.1 (A.dnPt P c g)) : Matrix (Fin n) (Fin n) E) *ᵥ x)) =
      Submodule.Quotient.mk ⟨_, h1⟩ := redL_coe ⟨_, h1⟩
  rw [hms, f_dnPt ht P hM c hg, e, extF_of_mem g (le_locP _ _ h1), h4] at h3
  exact (fv_mk hl P _ ⟨_, hsx⟩).trans h3.symm

omit [NumberField K] [StarRing K] in

theorem exists_smul_mem_N {SG : Finset (HeightOneSpectrum (𝓞 E))} {d : Deco E n ST SG} (hd : d.Ok) {a : 𝓞 E} (ha : SepElt ST a) (P : ST)
    {y : Fin n → E} (hy : y ∈ d.Lsh) : ∃ s : 𝓞 E, s ∉ P.1.asIdeal ∧ s • y ∈ d.N := by
  have h := le_locP P.1 _ hy
  rw [localization_Lsh_eq_localization_N hd ha P rfl] at h
  exact (mem_locP _ _ _).1 h

end TD

end GlobalTheory.DnFv

end

open GlobalTheory.LvT.Pts GlobalTheory.Mem.Col2.LvProj in
open Formalism.HermitianLatticesTheory (localization₂ dual) in
set_option maxHeartbeats 4000000 in

theorem GlobalTheory.Mem.Col2.TC.dn_level_functional : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (i : ℕ) (hi : i ≤ B.R.m) (bad : Set (HeightOneSpectrum (𝓞 B.host.F))) (Ch : Type) (chOf : (I.stp u a i).Cl → Ch) (K : ∀ β : Ch, LevelChart (I.rec7 l Z) (B.T u) bad i hi (fun c : {c // chOf c = β} => (I.chain l u a).stab i c.1) (fun c => latCrd (I.rec7 l Z) i hi (I.latAt u a i c.1))) (eY : (I.chain l u a).Y i ≃ Formalism.L2.Forms.Fr (I.rec7 l Z) i hi) (eV : (I.atT l u a).vT ≃ {v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F) // (B.T u : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal}) (L : LevelCompatibleLattices (D := (I.rec7 l Z)) (I.fm l u a) (B.T u) (I.resT l u a) i hi fun c => latCrd (I.rec7 l Z) i hi (I.latAt u a i c)), I.ReadsK l Z u a i hi chOf K → I.IdY l Z u a i hi eY → I.IdV l u a eV → I.IdL l Z u a i hi L → ∀ (v : (I.atT l u a).vT) (β : Ch) (c : {c // chOf c = β}) (g : Module.Dual (Res v.1) (((I.atIn u a).A i).lk v c.1)), g ≠ 0 → ∀ (γ : UJ (sigD (I.rec7 l Z) : (I.rec7 l Z).host.E →+* (I.rec7 l Z).host.E) (gramN (I.rec7 l Z) i hi)), (γ.1 : GL (Fin (B.R.N i)) B.fields.E) = (I.stp u a i).gam c.1.1 ((I.stp u a i).mv c.1.1 (((I.atIn u a).A i).dnPt v c.1 g)) → ∀ (x : ↥(LdG (I.rec7 l Z) i hi (latCrd (I.rec7 l Z) i hi (I.latAt u a i ((I.fm l u a).dn i v c.1 g))))) (hx : γ.1.1 *ᵥ x.1 ∈ LkG (I.rec7 l Z) i hi (PvG (I.resT l u a) v) (latCrd (I.rec7 l Z) i hi (I.latAt u a i c.1))), (I.fm l u a).fv i v _ (L.pr v _ x) = g (L.prk v c.1 ⟨_, hx⟩) := by
  intro B X I hI hP l Z u a i hi bad Ch chOf K eY eV L hK hY hV hL v β c g hg γ hγ x hx
  obtain ⟨-, -, -, hc⟩ := TC.spaces_in_coordinates I hI hP l Z
  obtain ⟨hgr, -, hc⟩ := hc i hi
  have hLc := (hc u a).1
  clear hc
  have ha := sepElt_of_ok l.pr u
  have hmv := moveHyp_of_ok l.pr u v
  have hM : MoveHyp ((B.primes X).vT u) ∅ v := ⟨hmv.ne, hmv.st, fun w => absurd w.2 (Finset.notMem_empty _)⟩
  have hd : ∀ c', (((I.stp u a i).rep c').1.1.deco.1).Ok := fun c' => ((I.stp u a i).rep c').1.1.deco.2
  have hD : ∀ c', LdG (I.rec7 l Z) i hi (latCrd (I.rec7 l Z) i hi (I.latAt u a i c')) = (((I.stp u a i).rep c').1.1.deco.1).Lsh := fun c' =>
    (@dualL_one B.fields.E B.fields.fieldE B.fields.nfE B.fields.starE _ (sigD (I.rec7 l Z) : (I.rec7 l Z).host.E →+* (I.rec7 l Z).host.E) (fun _ => rfl) _ hgr _).trans (congrArg _ (hLc c'))
  have hx2 : (x.1 : Fin (B.R.N i) → B.fields.E) ∈ (((I.stp u a i).rep ((I.fm l u a).dn i v c.1 g)).1.1.deco.1).Lsh :=
    (SetLike.ext_iff.1 (hD _) _).1 x.2
  obtain ⟨s, hs, hsx⟩ := GlobalTheory.DnFv.exists_smul_mem_N (hd _) ha v hx2
  have hγ' : (γ.1.1 : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) B.fields.E) = _ := congrArg Units.val hγ
  obtain ⟨h1, h2⟩ := GlobalTheory.DnFv.fv_dn ((l.lev u a).lev i) ((l.lev u a).tied i) ((l.fmL u a).lev i) v hM c.1 hg hγ' hsx
  let s' : 𝓞 (I.rec7 l Z).host.E := s
  have hs' : (Ideal.Quotient.mk v.1.asIdeal s : Res v.1) ≠ 0 := mk_ne_zero hs
  have f1 : ((I.fm l u a).fv i v _ (L.pr v _ (s' • x)) : Res v.1) =
      (Ideal.Quotient.mk v.1.asIdeal s : Res v.1) * (I.fm l u a).fv i v _ (L.pr v _ x) :=
    (congrArg ((I.fm l u a).fv i v ((I.fm l u a).dn i v c.1 g)) (L.pr_smul v _ s' x)).trans
      (GlobalTheory.DnFv.dual_map_smul ((I.fm l u a).fv i v ((I.fm l u a).dn i v c.1 g)) _ _)
  let z : ↥(LkG (I.rec7 l Z) i hi (PvG (I.resT l u a) v) (latCrd (I.rec7 l Z) i hi (I.latAt u a i c.1))) := ⟨_, hx⟩
  have f2 : (g (L.prk v c.1 (s' • z)) : Res v.1) =
      (Ideal.Quotient.mk v.1.asIdeal s : Res v.1) * g (L.prk v c.1 z) :=
    (congrArg g (L.prk_smul v c.1 s' z)).trans (GlobalTheory.DnFv.dual_map_smul g _ _)
  refine mul_left_cancel₀ hs' (f1.symm.trans (Eq.trans ?_ f2))
  have e1 := hL.1 v _ (s' • x) hsx
  have e2 := hL.2 v c.1 (s' • z) h1
  exact (congrArg _ e1).trans (h2.trans (congrArg g e2.symm))
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormInfIsometryConjLeConstMul
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix Formalism.IndefR.Datum
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Isom

theorem sum_norm_conj_le {m n : ℕ} (P : Matrix (Fin m) (Fin n) ℂ) (A : Matrix (Fin n) (Fin n) ℂ)
    (Q : Matrix (Fin n) (Fin m) ℂ) :
    ∑ i, ∑ j, ‖(P * A * Q) i j‖ ≤
      ((m : ℝ) * m * (∑ i, ∑ k, ‖P i k‖) * (∑ l, ∑ j, ‖Q l j‖)) * ∑ k, ∑ l, ‖A k l‖ := by
  set cP := ∑ i, ∑ k, ‖P i k‖
  set cQ := ∑ l, ∑ j, ‖Q l j‖
  set S := ∑ k, ∑ l, ‖A k l‖
  have hP : ∀ i k, ‖P i k‖ ≤ cP := fun i k =>
    (Finset.single_le_sum (f := fun k => ‖P i k‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ k)).trans
      (Finset.single_le_sum (f := fun i => ∑ k, ‖P i k‖) (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _)
        (Finset.mem_univ i))
  have hQ : ∀ l j, ‖Q l j‖ ≤ cQ := fun l j =>
    (Finset.single_le_sum (f := fun j => ‖Q l j‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ j)).trans
      (Finset.single_le_sum (f := fun l => ∑ j, ‖Q l j‖) (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _)
        (Finset.mem_univ l))
  have hcP : 0 ≤ cP := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hcQ : 0 ≤ cQ := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hent : ∀ i j, ‖(P * A * Q) i j‖ ≤ cP * cQ * S := by
    intro i j
    have e : (P * A * Q) i j = ∑ l, ∑ k, P i k * A k l * Q l j := by
      simp only [Matrix.mul_apply, Finset.sum_mul]
    rw [e]
    calc ‖∑ l, ∑ k, P i k * A k l * Q l j‖ ≤ ∑ l, ∑ k, ‖P i k‖ * ‖A k l‖ * ‖Q l j‖ := by
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => (norm_sum_le _ _).trans (le_of_eq ?_))
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [norm_mul, norm_mul]
      _ ≤ ∑ l, ∑ k, cP * ‖A k l‖ * cQ := by
          refine Finset.sum_le_sum fun l _ => Finset.sum_le_sum fun k _ => ?_
          exact mul_le_mul (mul_le_mul_of_nonneg_right (hP i k) (norm_nonneg _)) (hQ l j) (norm_nonneg _)
            (mul_nonneg hcP (norm_nonneg _))
      _ = cP * cQ * S := by
          rw [Finset.sum_comm]
          simp only [S, Finset.mul_sum]
          refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
          ring
  calc ∑ i, ∑ j, ‖(P * A * Q) i j‖ ≤ ∑ _i : Fin m, ∑ _j : Fin m, cP * cQ * S :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hent i j
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

theorem normInf_kap_le : ∀ (D : D7) (V V' : HSp D) (I : GlobalTheory.Mem.Isom.IsoMat V V') (θ : InfF D), IsInfFam θ →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ g : GA D V, normInf θ V' (I.kap g) ≤ C * normInf θ V g := by
  intro D V V' I θ hθ
  let K : D.what₂.Tau → ℝ := fun τ =>
    (V'.rank : ℝ) * V'.rank * (∑ i, ∑ k, ‖I.pT τ i k‖) * (∑ l, ∑ j, ‖I.qT τ l j‖)
  have hK : ∀ τ, 0 ≤ K τ := fun τ => by positivity
  refine ⟨∑ τ, K τ, Finset.sum_nonneg fun τ _ => hK τ, fun g => ?_⟩
  unfold normInf
  have key : ∀ τ, (∑ i, ∑ j, (‖infMat D.sp.cm.sig V'.gram (θ τ) (I.kap g) i j‖ +
      ‖infMat D.sp.cm.sig V'.gram (θ τ) (I.kap g)⁻¹ i j‖)) ≤
      K τ * ∑ i, ∑ j, (‖infMat D.sp.cm.sig V.gram (θ τ) g i j‖ + ‖infMat D.sp.cm.sig V.gram (θ τ) g⁻¹ i j‖) := by
    intro τ
    rw [← map_inv I.kap g, I.infMat_kap hθ, I.infMat_kap hθ]
    simp only [Finset.sum_add_distrib, mul_add]
    exact add_le_add (sum_norm_conj_le _ _ _) (sum_norm_conj_le _ _ _)
  have hS : ∀ τ, 0 ≤ ∑ i, ∑ j, (‖infMat D.sp.cm.sig V.gram (θ τ) g i j‖ +
      ‖infMat D.sp.cm.sig V.gram (θ τ) g⁻¹ i j‖) := fun τ => by positivity
  calc _ ≤ ∑ τ, K τ * ∑ i, ∑ j, (‖infMat D.sp.cm.sig V.gram (θ τ) g i j‖ +
          ‖infMat D.sp.cm.sig V.gram (θ τ) g⁻¹ i j‖) := Finset.sum_le_sum fun τ _ => key τ
    _ ≤ ∑ τ, (∑ σ, K σ) * ∑ i, ∑ j, (‖infMat D.sp.cm.sig V.gram (θ τ) g i j‖ +
          ‖infMat D.sp.cm.sig V.gram (θ τ) g⁻¹ i j‖) :=
        Finset.sum_le_sum fun τ _ => mul_le_mul_of_nonneg_right
          (Finset.single_le_sum (fun σ _ => hK σ) (Finset.mem_univ τ)) (hS τ)
    _ = _ := by rw [← Finset.mul_sum]

end GlobalTheory.Mem.Isom
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PairingComplexFormsConstOnRowClasses
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Df

attribute [local instance] GlobalTheory.Mem.Col2.starE

namespace GlobalTheory.Mem.Df

variable {X : Fields} {n : ℕ}
open Matrix

theorem ufGL_apply_single (γ : UF X.E n) (i j : Fin n) :
    ((ufGL X.E n γ : GL (Fin n) X.E) : Matrix (Fin n) (Fin n) X.E) i j = (γ.1 (Pi.single j 1)) i := by
  simp [ufGL, toGLm, Matrix.GeneralLinearGroup.toLin, LinearMap.GeneralLinearGroup.generalLinearEquiv]

theorem ufGL_unitary (γ : UF X.E n) :
    ((ufGL X.E n γ : GL (Fin n) X.E) : Matrix (Fin n) (Fin n) X.E)ᴴ * (ufGL X.E n γ : Matrix (Fin n) (Fin n) X.E) = 1 := by
  ext j k
  have h := γ.2 (Pi.single j 1) (Pi.single k 1)
  simp only [hStd, LinearMap.mk₂'ₛₗ_apply] at h
  rw [Matrix.mul_apply]
  simp only [Matrix.conjTranspose_apply, ufGL_apply_single]
  rw [h]
  simp only [Pi.single_apply, Matrix.one_apply]
  simp [eq_comm]
  split_ifs <;> simp

theorem bc_conj_unitary (hX : X.Ok) (φ : X.E →+* ℂ) (γ : UF X.E n) :
    Formalism.UG.bc (starRingEnd ℂ) (Formalism.UG.bc φ (ufGL X.E n γ)) = inside₂ ℂ n (Formalism.UG.bc φ (ufGL X.E n γ)) := by
  set A := Formalism.UG.bc φ (ufGL X.E n γ)
  have hA : (A : Matrix (Fin n) (Fin n) ℂ) = (ufGL X.E n γ : Matrix (Fin n) (Fin n) X.E).map φ := rfl
  have h1 : ((A : Matrix (Fin n) (Fin n) ℂ).map (starRingEnd ℂ))ᵀ * (A : Matrix (Fin n) (Fin n) ℂ) = 1 := by
    have := congrArg (fun M => M.map φ) (ufGL_unitary γ)
    simp only [Matrix.map_mul, Matrix.map_one _ φ.map_zero φ.map_one] at this
    rw [← this, hA]
    congr 1
    ext i j
    simp [Matrix.conjTranspose_apply, hX.conjE]
  apply Units.ext
  show (A : Matrix (Fin n) (Fin n) ℂ).map (starRingEnd ℂ) = ((A⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)ᵀ
  have h2 : ((A : Matrix (Fin n) (Fin n) ℂ).map (starRingEnd ℂ))ᵀ = ((A⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) := by
    calc _ = ((A : Matrix (Fin n) (Fin n) ℂ).map (starRingEnd ℂ))ᵀ * ((A : Matrix (Fin n) (Fin n) ℂ) * ((A⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)) := by
            rw [← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
      _ = _ := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  rw [← h2, Matrix.transpose_transpose]

theorem map_conj_rhoC (hX : X.Ok) (σ : X.K →+* ℂ) (lam : X.Tau → DomWeight n) (γ : UF X.E n) (p : Pol ℂ X.Tau n) :
    MvPolynomial.map (starRingEnd ℂ) (rhoC σ lam γ p) =
      actP lam (invTrK (embGL (embAt σ X.emb) (ufGL X.E n γ))) (MvPolynomial.map (starRingEnd ℂ) p) := by
  rw [rhoC_apply]
  refine (GlobalTheory.ValCmp.use₂ (starRingEnd ℂ) lam _ p).trans ?_
  congr 2
  funext τ
  exact bc_conj_unitary hX (embAt σ X.emb τ) γ

theorem pairB_rhoC (hX : X.Ok) (σ : X.K →+* ℂ) (lam : X.Tau → DomWeight n) (γ : UF X.E n) (p q : Pol ℂ X.Tau n) :
    pairB lam (MvPolynomial.map (starRingEnd ℂ) (rhoC σ lam γ p)) (rhoC σ lam γ q) =
      pairB lam (MvPolynomial.map (starRingEnd ℂ) p) q := by
  rw [map_conj_rhoC hX σ lam γ p, rhoC_apply]
  exact pairingBInvariantK_holds ℂ X.Tau n lam _ _ q

theorem conj_mul_self_chr {SG : Finset (HeightOneSpectrum (𝓞 X.E))} (σ : X.K →+* ℂ) (Λ : LevFam X.E X.K n SG) (h : ↥Λ.grp) :
    starRingEnd ℂ (σ (Λ.chr h : X.Kˣ)) * σ (Λ.chr h : X.Kˣ) = 1 := by
  obtain ⟨N, hN, hp⟩ := (isOfFinOrder_of_finite h).exists_pow_eq_one
  have h1 : (σ (Λ.chr h : X.Kˣ)) ^ N = 1 := by
    rw [← map_pow, ← Units.val_pow_eq_pow_val, ← map_pow, hp, map_one, Units.val_one, map_one]
  have h2 := Complex.norm_eq_one_of_pow_eq_one h1 hN.ne'
  rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, h2]
  simp

theorem pairB_conj_cls_eq : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X) (hX : B.fields.Ok) (a : I.ι) (F G : MtCx I a)
    (d d' : (rowS I a).D), (rowS I a).cls d = (rowS I a).cls d' →
    pairB B.wts.sgTrue (MvPolynomial.map (starRingEnd ℂ) (F.1 d)) (G.1 d) =
      pairB B.wts.sgTrue (MvPolynomial.map (starRingEnd ℂ) (F.1 d')) (G.1 d') := by
  intro B X I hX a F G d d' h
  obtain ⟨g, rfl⟩ := ((rowS I a).cls_eq_iff _ _).1 h
  have hF := (F.2 d').2 g
  have hG := (G.2 d').2 g
  letI := (rowS I a).actD
  erw [hF, hG]
  rw [map_conj_smul, LinearMap.map_smul, LinearMap.map_smul, LinearMap.smul_apply]
  rw [pairB_rhoC hX, smul_eq_mul, smul_eq_mul, ← mul_assoc, mul_comm (B.embLL _)]
  have hc := conj_mul_self_chr B.embLL (rowTy I.Ch I.sel (I.tup a) I.Ps).inv g.2
  rw [hc, one_mul]

example : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X) (hX : B.fields.Ok) (a : I.ι) (F G : MtCx I a) (d d' : (rowS I a).D), (rowS I a).cls d = (rowS I a).cls d' → pairB B.wts.sgTrue (MvPolynomial.map (starRingEnd ℂ) (F.1 d)) (G.1 d) = pairB B.wts.sgTrue (MvPolynomial.map (starRingEnd ℂ) (F.1 d')) (G.1 d') := pairB_conj_cls_eq

end GlobalTheory.Mem.Df
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RatIsom
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Cartier GlobalTheory.CxPts

namespace GlobalTheory.HermIsom

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k}

def RatIsom [IsIntegral X] (L M : HermLB p) : Prop :=
  ∃ (Δ : CartierDiv X) (r : L.B.ι → X.functionFieldˣ) (s : M.B.ι → X.functionFieldˣ),
    Presents Δ L.B r ∧ Presents Δ M.B s ∧ ∀ (σ : k →+* ℂ) (y : CxPts p σ) (i : L.B.ι) (j : M.B.ι),
      y ∈ ptsIn p σ (L.B.U i) → y ∈ ptsIn p σ (M.B.U j) →
        (M.φ σ).φ j y = (L.φ σ).φ i y + Real.log (‖ratVal ((s j / r i : X.functionFieldˣ) : X.functionField) y‖ ^ 2)

end GlobalTheory.HermIsom
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReFaceScalarsErrorsReadings
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

noncomputable section

namespace GlobalTheory.Mem.R3

set_option maxHeartbeats 4000000 in

theorem reFace_scalars_errors_readings : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y) (Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 F.P1 F.ψ1 Zs)) (Sp : ∀ Zs, SPer (Dc Zs)) (Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3), (∀ i, (Zsc (R.toCx3 F).zs).l6m i = (F.Zsc (R.toCx3 F).zs).l6m i ∨ ((∀ p, R.Wp3 i p ≠ ⊥) ∧ ∀ p v, v ≠ A3.A.v0 → R.PartAt F i p v)) → Pins R F cG → Holds R F → ∃ kap lam err, Pins ((R.updS kap lam).withErr err) (reFace F Dc Sp Zsc) cG ∧ Holds ((R.updS kap lam).withErr err) (reFace F Dc Sp Zsc) ∧ ErrEq ((R.updS kap lam).withErr err) (reFace F Dc Sp Zsc) ∧ kap = R.kap ∧ (∀ i t p v, R.Wp3 i p ≠ ⊥ → lam i t p v = R.lam3 i t p v) ∧ ∃ (Y' : Read (A3 := A3) ((R.updS kap lam).withErr err).toRealDat (reFace F Dc Sp Zsc).lv2 X0) (Z' : ReadL ((R.updS kap lam).withErr err) (reFace F Dc Sp Zsc) X0 Y'), Y'.tup = Y.tup ∧ Y'.tupT = Y.tupT ∧ HEq Y'.jA Y.jA ∧ HEq Y'.jA0 Y.jA0 ∧ HEq Y'.eMt Y.eMt ∧ HEq Y'.PY Y.PY ∧ HEq Y'.eFT Y.eFT ∧ HEq Y'.IL Y.IL ∧ HEq Z'.jW Z.jW := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y Z Dc Sp Zsc hl6 hP hH
  refine ⟨R.kap, R.lam3, reFaceErr R F Dc Sp Zsc, ?_⟩
  exact ⟨reFace_pins R F cG Dc Sp Zsc _ hl6 hP,
    ⟨reFace_prim R F Dc Sp Zsc _ hH.prim, further_face_statements_independent_of_error R F Dc Sp Zsc _ hH.aux, hH.ok, hH.sep⟩,
    reFace_errEq R F Dc Sp Zsc, rfl, fun _ _ _ _ _ => rfl,
    reFaceRead R F Dc Sp Zsc _ X0 Y, reFaceReadL R F Dc Sp Zsc _ X0 Y Z,
    rfl, rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl⟩

end GlobalTheory.Mem.R3

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadsOfLocMv
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.TC.ChTw

variable {B : Base} {X : PreX B.toPre} (I : TC B X)

def LocMv (u : B.Word) (a : I.ι) (i : ℕ) (c : (I.stp u a i).Cl) (s : GA B (B.R.N i)) (κ : (I.stp u a i).G c.1) : Prop :=
  (I.stp u a i).gam c.1 κ = 1 ∧
    cosetIn ((I.stp u a i).act c.1 κ ((I.stp u a i).rep c)) = cosetIn ((I.stp u a i).rep c) ∧
    ∀ g : GA B (B.R.N i), PtOf g ((I.stp u a i).rep c).1.1 → PtOf (g * s) ((I.stp u a i).act c.1 κ ((I.stp u a i).rep c)).1.1

theorem reads_of_locMv (hI : I.Ok) {u : B.Word} {a : I.ι} {i : ℕ} {Ch : Type} {chOf : (I.stp u a i).Cl → Ch}
    {Lb : Ch → Submodule (𝓞 B.host.E) (Fin (B.R.N i) → B.host.E)} {U : Ch → Subgroup (GA B (B.R.N i))} {chi : ∀ β, U β →* ℂˣ}
    {y : (I.stp u a i).Cl → GA B (B.R.N i)} {st : ∀ c, (I.stp u a i).Stab c → GL (Fin (B.R.N i)) B.host.E}
    {k : Ch → GA B (B.R.N i)} (hR : I.Reads u a i chOf Lb U chi y st k) (c : (I.stp u a i).Cl) (x : GA B (B.R.N i))
    (κ : (I.stp u a i).G c.1) (h : LocMv I u a i c ((k (chOf c))⁻¹ * x * k (chOf c)) κ) :
    ∃ hx : x ∈ U (chOf c), ((chi (chOf c) ⟨x, hx⟩ : ℂˣ) : ℂ) = B.embLL (((I.stp u a i).chr c.1 κ : B.LLˣ) : B.LL) := by
  have hd : Disjoint (B.primes X).vGs (I.Q a) :=
    Finset.disjoint_of_subset_right (ColIn.Q_subset_SQ I a) (GlobalTheory.Mem.LevTwist.levOk_twists B X I hI).2.1
  have hp : PtOf (y c * k (chOf c)) ((I.stp u a i).rep c).1.1 :=
    IsPtOf.of_extTo (ColIn.Q_subset_SQ I a) hd (hR.pt c)
  have e : y c * k (chOf c) * ((k (chOf c))⁻¹ * x * k (chOf c)) = y c * x * k (chOf c) := by group
  have hq := h.2.2 _ hp
  rw [e] at hq
  have hx : x ∈ U (chOf c) := (hR.lev c x _ hq).2 ⟨κ, h.1, rfl, h.2.1⟩
  exact ⟨hx, hR.chr c ⟨x, hx⟩ κ h.1 hq⟩

end GlobalTheory.Mem.Col2.TC.ChTw
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RedMLevJ
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.Mem.Col2.TC.LevJRed

attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {gp : Fin 2 → ℕ}

theorem mat_one (G : GLoc F E σ gp) (j : Fin 2) (v : HeightOneSpectrum (𝓞 F)) (h : (gp j : 𝓞 F) ∈ v.asIdeal)
    (fr : GL (Fin n) (v.adicCompletion F)) : G.mat j v h fr 1 = 1 := by
  unfold GLoc.mat
  rw [map_one, mul_one, inv_mul_cancel, Units.val_one]

theorem mat_mul (G : GLoc F E σ gp) (j : Fin 2) (v : HeightOneSpectrum (𝓞 F)) (h : (gp j : 𝓞 F) ∈ v.asIdeal)
    (fr : GL (Fin n) (v.adicCompletion F)) (x y : GL (Fin n) (E ⊗[F] v.adicCompletion F)) :
    G.mat j v h fr (x * y) = G.mat j v h fr x * G.mat j v h fr y := by
  unfold GLoc.mat
  rw [map_mul, ← Units.val_mul]
  congr 1
  group

theorem mat_int (G : GLoc F E σ gp) (j : Fin 2) (v : HeightOneSpectrum (𝓞 F)) (h : (gp j : 𝓞 F) ∈ v.asIdeal)
    {J : Matrix (Fin n) (Fin n) E} {Lb : Submodule (𝓞 E) (Fin n → E)} (fr : GL (Fin n) (v.adicCompletion F))
    (hfr : ∀ x : Fin n → v.adicCompletion F,
      (∃ y ∈ latS (F := F) (v.adicCompletion F) (intV E v) Lb, ∀ b, G.phi j v h (y b) = x b) ↔
        ∀ b, ((fr⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)).mulVec x b ∈
          v.adicCompletionIntegers F)
    {x : GL (Fin n) (E ⊗[F] v.adicCompletion F)} (hx : x ∈ levelVL σ J v Lb) (a b : Fin n) :
    G.mat j v h fr x a b ∈ v.adicCompletionIntegers F := by
  classical
  set w : Fin n → v.adicCompletion F := (fr : Matrix (Fin n) (Fin n) (v.adicCompletion F)) *ᵥ Pi.single b 1 with hw
  have hinv : ((fr⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) *ᵥ w = Pi.single b 1 := by
    rw [hw, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  obtain ⟨y, hy, hyw⟩ := (hfr w).2 fun c => by
    rw [hinv]
    by_cases e : c = b
    · subst e
      rw [Pi.single_eq_same]
      exact one_mem _
    · rw [Pi.single_eq_of_ne e]
      exact zero_mem _
  have hst : x ∈ stabGL (latS (F := F) (v.adicCompletion F) (intV E v) Lb) := hx.2
  have hxy : (x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *ᵥ y ∈
      latS (F := F) (v.adicCompletion F) (intV E v) Lb := (hst y).1 hy
  have hphi : ∀ c, G.phi j v h (((x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *ᵥ y) c) =
      (((x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)).map (G.phi j v h)) *ᵥ w) c := by
    intro c
    simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply, hyw]
  have key := (hfr _).1 ⟨_, hxy, hphi⟩ a
  convert key using 1
  unfold GLoc.mat
  rw [hw, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Units.val_mul, Units.val_mul, Matrix.mulVec_single_one]
  rfl

end Gen

theorem redM_levJ : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) {Ch0 : ℕ → Type} {chOf0 : ∀ i, ((I.rec7 l Z).mem u).C.cls i → Ch0 i} (F : FormsTiedSym (I.rec7 l Z) u Ch0 chOf0), I.StdF l Z u F → ∀ (j : Fin 2) (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)) (hv : ((I.rec7 l Z).host.g j : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal), redM (I.rec7 l Z).host.F v (F.gl.mat j v hv (F.glevJ.fr j v hv) 1) = 1 ∧ ∀ x ∈ F.levJ.Uloc v, ∀ y ∈ F.levJ.Uloc v, redM (I.rec7 l Z).host.F v (F.gl.mat j v hv (F.glevJ.fr j v hv) (x * y)) = redM (I.rec7 l Z).host.F v (F.gl.mat j v hv (F.glevJ.fr j v hv) x) * redM (I.rec7 l Z).host.F v (F.gl.mat j v hv (F.glevJ.fr j v hv) y) := by
  intro B X I _ _ l Z u Ch0 chOf0 F _ j v hv
  have hint : ∀ x ∈ F.levJ.Uloc v, ∀ a b, F.gl.mat j v hv (F.glevJ.fr j v hv) x a b ∈
      v.adicCompletionIntegers (I.rec7 l Z).host.F := fun x hx =>
    mat_int F.gl j v hv (F.glevJ.fr j v hv) (F.glevJ.fr_lat j v hv) (F.levJ.Uloc_lev v hx)
  refine ⟨?_, fun x hx y hy => ?_⟩
  · rw [mat_one]
    exact ChartLevel.redM_one v
  · rw [mat_mul]
    exact ChartLevel.redM_mul v (hint x hx) (hint y hy)

end GlobalTheory.Mem.Col2.TC.LevJRed
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ResidueFieldEquivRealSubfieldQuotientTrueColumnsStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.residueField_equiv_realSubfieldQuotient_trueColumns : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) {Ch : ℕ → Type} {chOf : ∀ i, ((I.rec7 l Z).mem u).C.cls i → Ch i} (F : FormsTiedSym (I.rec7 l Z) u Ch chOf), I.StdF l Z u F → ∀ v : ((I.rec7 l Z).mem u).A.vT,
  ∃ e : ((I.rec7 l Z).mem u).A.Fv v ≃+* (𝓞 (I.rec7 l Z).host.F ⧸ (F.atT.eV v).1.asIdeal),
    ∀ a : 𝓞 (I.rec7 l Z).host.F, e (F.atT.res v (algebraMap (𝓞 (I.rec7 l Z).host.F) (𝓞 (I.rec7 l Z).host.E) a)) = Ideal.Quotient.mk _ a := by
  first | exact @GlobalTheory.Mem.Col2.ResF.fv_equiv_quot | exact GlobalTheory.Mem.Col2.ResF.fv_equiv_quot | (intros; apply GlobalTheory.Mem.Col2.ResF.fv_equiv_quot <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RieszVectorsPureTensorsInnerEqProdStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.riesz_vectors_pure_tensors_inner_eq_prod : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.BaseW F → Seed.PrIso R.MX R.cX R.prX → ∀ (v v' : R.MX.Vec) (a a' : R.cX.W), (∀ w, R.prX w (PiTensorProduct.tprod ℂ v) = ⟪a, w⟫_ℂ) → (∀ w, R.prX w (PiTensorProduct.tprod ℂ v') = ⟪a', w⟫_ℂ) → ⟪a', a⟫_ℂ = ∏ τ, ⟪(v τ : R.MX.H τ), (v' τ : R.MX.H τ)⟫_ℂ := by
  first | exact @GlobalTheory.Mem.rieszProd_inner | exact GlobalTheory.Mem.rieszProd_inner | (intros; apply GlobalTheory.Mem.rieszProd_inner <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StandardAddCharPlaceIdempotentDivPrimeStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.standardAddChar_placeIdempotent_div_prime : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (p : ℕ), p.Prime → ∀ (v : HeightOneSpectrum (𝓞 D.host.F)), Ideal.absNorm v.asIdeal = p → (p : 𝓞 D.host.F) ∉ v.asIdeal ^ 2 → ∀ ε, IsPlaceIdem D v ε → ∀ (a : 𝓞 D.host.F) (b : ℤ), a - (b : 𝓞 D.host.F) ∈ v.asIdeal → ψ (ε * algebraMap D.host.F (AF D.host.F) ((a : D.host.F) / (p : D.host.F))) = Complex.exp (2 * Real.pi * Complex.I * b / (p : ℂ)) := by
  first | exact @GlobalTheory.StdCharDegOne.stdChar_placeIdem_div | exact GlobalTheory.StdCharDegOne.stdChar_placeIdem_div | (intros; apply GlobalTheory.StdCharDegOne.stdChar_placeIdem_div <;> assumption)
end

