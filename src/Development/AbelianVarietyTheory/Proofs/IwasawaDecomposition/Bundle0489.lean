import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0028
import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0014
import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.ComparisonZeroEmbedding
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0483
import Formalism.LocalRingCardinality.FactDelDualNabla
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0022
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0105
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NVNeZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0479
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0450
import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.ComplexMultiplication.ExtEmbEquivComp

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFreeSeriesKernelServedPlace
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.KerTieServed
open MvPowerSeries

section Lin
variable {p : ℕ} [Fact p.Prime] {σ σ' : Type*} [Fintype σ] [Fintype σ']

theorem hasSubst_linear {κ : Type*} [Fintype κ] (c : σ → κ → ℂ_[p]) :
    HasSubst (fun k : σ => ∑ x : κ, algebraMap ℂ_[p] (MvPowerSeries κ ℂ_[p]) (c k x) * X x) :=
  hasSubst_of_constantCoeff_zero fun k => by simp

theorem linAt_comp {κ : Type*} [Fintype κ] (c₁ : σ → σ' → ℂ_[p]) (c₂ : σ' → κ → ℂ_[p]) (F : MvPowerSeries σ ℂ_[p]) :
    linAt c₂ (linAt c₁ F) = linAt (fun k x => ∑ j, c₁ k j * c₂ j x) F := by
  unfold linAt
  rw [subst_comp_subst_apply (hasSubst_linear c₁) (hasSubst_linear c₂)]
  congr 1
  funext k
  rw [← coe_substAlgHom (hasSubst_linear c₂)]
  simp only [map_sum, map_mul, AlgHom.commutes, substAlgHom_X, Finset.mul_sum, Finset.sum_mul, mul_assoc]
  rw [Finset.sum_comm]

theorem linAt_delta [DecidableEq σ] (F : MvPowerSeries σ ℂ_[p]) :
    linAt (fun k x : σ => if k = x then (1 : ℂ_[p]) else 0) F = F := by
  unfold linAt
  have e : (fun k : σ => ∑ x : σ, algebraMap ℂ_[p] (MvPowerSeries σ ℂ_[p]) (if k = x then (1 : ℂ_[p]) else 0) * X x) =
      X := by
    funext k
    simp [apply_ite]
  rw [e, subst_self]
  rfl

end Lin

section Mat
variable {K : Type*} [Field K] {T J I : Type*} [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]

def blk (ev : T → Prop) [DecidablePred ev] (A : T → Matrix J J K) (e : I ≃ J) (τ : T) : Matrix J I K :=
  if ev τ then (A τ).submatrix id e else ((A τ)⁻¹).transpose.submatrix id e

def blkInv (ev : T → Prop) [DecidablePred ev] (A : T → Matrix J J K) (e : I ≃ J) (τ : T) : Matrix I J K :=
  if ev τ then ((A τ)⁻¹).submatrix e id else (A τ).transpose.submatrix e id

theorem blkInv_mul_blk (ev : T → Prop) [DecidablePred ev] (A : T → Matrix J J K) (e : I ≃ J)
    (hA : ∀ τ, IsUnit (A τ).det) (τ : T) : blkInv ev A e τ * blk ev A e τ = 1 := by
  unfold blk blkInv
  split_ifs
  · rw [← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id, Matrix.nonsing_inv_mul _ (hA τ),
      Matrix.submatrix_one_equiv]
  · rw [← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id, ← Matrix.transpose_mul, Matrix.nonsing_inv_mul _ (hA τ), Matrix.transpose_one,
      Matrix.submatrix_one_equiv]

end Mat

section Sum
variable {K : Type*} [CommRing K] {S T J₁ J₂ I₁ I₂ : Type*} [Fintype T] [DecidableEq T] [Fintype J₁] [Fintype J₂]
  [DecidableEq S] [DecidableEq I₁] [DecidableEq I₂] [DecidableEq J₁] [DecidableEq J₂]

def coef (t : S → T) (P : T → Matrix J₂ I₂ K) (Q : T → Matrix I₁ J₁ K) : T × J₂ × J₁ → S × I₁ × I₂ → K :=
  fun k x => if t x.1 = k.1 then P k.1 k.2.1 x.2.2 * Q k.1 x.2.1 k.2.2 else 0

def coefInv (t : S → T) (P' : T → Matrix I₂ J₂ K) (Q' : T → Matrix J₁ I₁ K) : S × I₁ × I₂ → T × J₂ × J₁ → K :=
  fun x k => if t x.1 = k.1 then P' k.1 x.2.2 k.2.1 * Q' k.1 k.2.2 x.2.1 else 0

theorem sum_coefInv_coef (t : S → T) (ht : Function.Injective t) (P : T → Matrix J₂ I₂ K) (Q : T → Matrix I₁ J₁ K)
    (P' : T → Matrix I₂ J₂ K) (Q' : T → Matrix J₁ I₁ K) (hP : ∀ τ, P' τ * P τ = 1) (hQ : ∀ τ, Q τ * Q' τ = 1)
    (x x' : S × I₁ × I₂) :
    ∑ k, coefInv t P' Q' x k * coef t P Q k x' = if x = x' then 1 else 0 := by
  rw [Fintype.sum_prod_type, Finset.sum_eq_single (t x.1)]
  · unfold coef coefInv
    simp only [if_true]
    by_cases hxx : t x'.1 = t x.1
    · have h1 : x'.1 = x.1 := ht hxx
      simp only [hxx, if_true]
      have e : ∀ y : J₂ × J₁, P' (t x.1) x.2.2 y.1 * Q' (t x.1) y.2 x.2.1 * (P (t x.1) y.1 x'.2.2 * Q (t x.1) x'.2.1 y.2) =
          (P' (t x.1) x.2.2 y.1 * P (t x.1) y.1 x'.2.2) * (Q (t x.1) x'.2.1 y.2 * Q' (t x.1) y.2 x.2.1) := fun y => by ring
      rw [Finset.sum_congr rfl fun y _ => e y, Fintype.sum_prod_type]
      simp only [← Finset.mul_sum, ← Finset.sum_mul]
      have e1 := congrFun (congrFun (hP (t x.1)) x.2.2) x'.2.2
      have e2 := congrFun (congrFun (hQ (t x.1)) x'.2.1) x.2.1
      rw [Matrix.mul_apply] at e1 e2
      rw [e1, e2, Matrix.one_apply, Matrix.one_apply]
      obtain ⟨a, b, c⟩ := x
      obtain ⟨a', b', c'⟩ := x'
      simp only at h1 ⊢
      subst h1
      rcases eq_or_ne b b' with rfl | hb <;> rcases eq_or_ne c c' with rfl | hc <;>
        first | (simp; done) | (simp [hb, hb.symm]; done) | (simp [hc, hc.symm]; done) | simp [hb, hb.symm, hc, hc.symm]
    · have hne : x ≠ x' := fun hx => hxx (by rw [hx])
      simp only [hxx, if_false, mul_zero, Finset.sum_const_zero, hne]
  · intro τ _ hτ
    refine Finset.sum_eq_zero fun y _ => ?_
    unfold coefInv
    rw [if_neg (Ne.symm hτ), zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

end Sum

section Main

theorem isUnit_det_rhoMat {D : D7} {Gt : GatTies D} {c : LatCmp D} {Tw : TwForms D} {u : D.what₂.Word} {w : D.what₂.places.Pl}
    {h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Fl : G.Fills (D.gat u w h)} {Lv : G.Levels Fl}
    {Ch : G.Chain Lv} (Kp : LocalToGlobal₂ D Gt c Tw u w h Ch) (j : ℕ) (τ : D.what₂.Tau)
    (g : ∀ v, Matrix (Fin ((Fl.Pj j).m + 1)) (Fin ((Fl.Pj j).m + 1)) ((Fl.Pj j).Qq v)) (hg : ∀ v, IsUnit (g v).det) :
    IsUnit (rhoMat Kp j τ g).det := by
  unfold rhoMat
  have e := RingHom.map_det (Kp.iK.comp (((Fl.Pj j).ι ((posJ Gt u w h Fl j).symm τ).1).comp
    (RingEquiv.toRingHom (((Fl.Pj j).σ ((posJ Gt u w h Fl j).symm τ).1) ^ ((posJ Gt u w h Fl j).symm τ).2.val))))
    (g ((posJ Gt u w h Fl j).symm τ).1)
  rw [RingHom.mapMatrix_apply] at e
  have hu := (hg ((posJ Gt u w h Fl j).symm τ).1).map (Kp.iK.comp (((Fl.Pj j).ι ((posJ Gt u w h Fl j).symm τ).1).comp
    (RingEquiv.toRingHom (((Fl.Pj j).σ ((posJ Gt u w h Fl j).symm τ).1) ^ ((posJ Gt u w h Fl j).symm τ).2.val))))
  rw [e] at hu
  exact hu

open Classical in

theorem exists_th_served : ∀ {D : D7} {Dx : DivX D} (Gt : GatTies D) {c : LatCmp D} {Tw : TwForms D} {u : D.what₂.Word} {w : D.what₂.places.Pl}
    {h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Fl : G.Fills (D.gat u w h)} {Lv : G.Levels Fl}
    (KD : Formalism.L2.G.Cmp.KerData D c Tw u w h Lv) (E : KerEnt D Dx Tw), KD.lam = E.lam w →
    ∃ Th, ThAtServed (Formalism.L2.G.Cmp.kerAtP_of Gt { KD with Th := Th }) E := by
  intro D Dx Gt c Tw u w h Fl Lv KD E hlam
  let g : ∀ (j : ℕ) (_ : Lv.comp j × (Fl.Pj j).Tup) (v : Fin (Fl.Pj j).nV),
      Matrix (Fin ((Fl.Pj j).m + 1)) (Fin ((Fl.Pj j).m + 1)) ((Fl.Pj j).Qq v) :=
    fun j La v => if hL : (Fl.Pj j).IsLatTup La.2 then (hL v).choose else 1
  have hg : ∀ j La v, IsUnit (g j La v).det := by
    intro j La v
    by_cases hL : (Fl.Pj j).IsLatTup La.2
    · simp only [g, dif_pos hL]; exact (hL v).choose_spec.1
    · simp only [g, dif_neg hL, Matrix.det_one]; exact isUnit_one
  let K0 := Formalism.L2.G.Cmp.kerAtP_of Gt KD
  let ev : ℕ → D.what₂.Tau → Prop := fun j τ => Formalism.MainNotions.G.IsTypeV ((posJ Gt u w h Fl j).symm τ).2
  let Th : ∀ j, Lv.comp j × (Fl.Pj j).Tup → Lv.comp (j + 1) × (Fl.Pj (j + 1)).Tup →
      MvPowerSeries (D.what₂.Tau × Fin ((Fl.Pj (j + 1)).m + 1) × Fin ((Fl.Pj j).m + 1)) ℂ_[D.what₂.places.resChar w] :=
    fun j La La' => if hh : (Fl.Pj j).m + 1 = D.R.N j ∧ (Fl.Pj (j + 1)).m + 1 = D.R.N (j + 1) then
      linAt (coefInv (Formalism.BasicNotions.tauPl D)
          (blkInv (ev j) (fun τ => rhoMat K0 (j + 1) τ (g (j + 1) La')) (finCongr hh.2.symm))
          (blk (ev j) (fun τ => rhoMat K0 j τ (g j La)) (finCongr hh.1.symm)))
        (E.Th u (D.what₂.muAt w) w j (KD.cls j La.1 La.2) (KD.cls (j + 1) La'.1 La'.2))
    else 0
  refine ⟨Th, hlam, g, ?_, ?_⟩
  · intro j _ La hL v
    refine ⟨hg j La v, ?_⟩
    simp only [g, dif_pos hL]
    exact (hL v).choose_spec.2
  · intro j _ hN hN' La La' _ _
    refine ⟨fun _ => 1, fun _ => norm_one, ?_⟩
    have hTh : Th j La La' = linAt (coefInv (Formalism.BasicNotions.tauPl D)
          (blkInv (ev j) (fun τ => rhoMat K0 (j + 1) τ (g (j + 1) La')) (finCongr hN'.symm))
          (blk (ev j) (fun τ => rhoMat K0 j τ (g j La)) (finCongr hN.symm)))
        (E.Th u (D.what₂.muAt w) w j (KD.cls j La.1 La.2) (KD.cls (j + 1) La'.1 La'.2)) := by
      simp only [Th, dif_pos (And.intro hN hN')]
    have hC : (fun (k : D.what₂.Tau × Fin ((Fl.Pj (j + 1)).m + 1) × Fin ((Fl.Pj j).m + 1))
              (x : (Bool × G.HH D) × Fin (D.R.N j) × Fin (D.R.N (j + 1))) =>
            if Formalism.BasicNotions.tauPl D x.1 = k.1 then
              (if Formalism.MainNotions.G.IsTypeV ((posJ Gt u w h Fl j).symm k.1).2 then
                (fun _ => (1 : ℂ_[D.what₂.places.resChar w])) k.1 * (rhoMat K0 (j + 1) k.1 (g (j + 1) La')) k.2.1 (Fin.cast hN'.symm x.2.2) *
                  ((rhoMat K0 j k.1 (g j La))⁻¹) (Fin.cast hN.symm x.2.1) k.2.2
              else
                (fun _ => (1 : ℂ_[D.what₂.places.resChar w])) k.1 * (((rhoMat K0 (j + 1) k.1 (g (j + 1) La'))⁻¹).transpose) k.2.1 (Fin.cast hN'.symm x.2.2) *
                  ((rhoMat K0 j k.1 (g j La)).transpose) (Fin.cast hN.symm x.2.1) k.2.2)
            else 0) =
        coef (Formalism.BasicNotions.tauPl D) (blk (ev j) (fun τ => rhoMat K0 (j + 1) τ (g (j + 1) La')) (finCongr hN'.symm))
          (blkInv (ev j) (fun τ => rhoMat K0 j τ (g j La)) (finCongr hN.symm)) := by
      funext k x
      simp only [coef, blk, blkInv, ev]
      split_ifs <;> simp [Matrix.submatrix_apply, Matrix.transpose_apply]
    have hS := sum_coefInv_coef (Formalism.BasicNotions.tauPl D) (Formalism.BasicNotions.tauPl_bij D).1
      (blk (ev j) (fun τ => rhoMat K0 (j + 1) τ (g (j + 1) La')) (finCongr hN'.symm))
      (blkInv (ev j) (fun τ => rhoMat K0 j τ (g j La)) (finCongr hN.symm))
      (blkInv (ev j) (fun τ => rhoMat K0 (j + 1) τ (g (j + 1) La')) (finCongr hN'.symm))
      (blk (ev j) (fun τ => rhoMat K0 j τ (g j La)) (finCongr hN.symm))
      (blkInv_mul_blk _ _ _ fun τ => isUnit_det_rhoMat K0 (j + 1) τ _ (hg (j + 1) La'))
      (blkInv_mul_blk _ _ _ fun τ => isUnit_det_rhoMat K0 j τ _ (hg j La))
    have key : E.Th u (D.what₂.muAt w) w j (KD.cls j La.1 La.2) (KD.cls (j + 1) La'.1 La'.2) =
        linAt (coef (Formalism.BasicNotions.tauPl D) (blk (ev j) (fun τ => rhoMat K0 (j + 1) τ (g (j + 1) La')) (finCongr hN'.symm))
          (blkInv (ev j) (fun τ => rhoMat K0 j τ (g j La)) (finCongr hN.symm))) (Th j La La') := by
      rw [hTh, linAt_comp]
      simp only [hS]
      exact (linAt_delta _).symm
    rw [← hC] at key
    exact key

end Main

end GlobalTheory.KerTieServed
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGlobalModuleLocalisingToLattices
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.Mem.Top.KerGlob

theorem weak_approx {F : Type} [Field F] [NumberField F] {ι : Type} [Fintype ι]
    (w : ι → HeightOneSpectrum (𝓞 F)) (hw : Function.Injective w) (y : ∀ i, (w i).adicCompletion F) (c : F) (hc : c ≠ 0) :
    ∃ a : F, ∀ i, Valued.v (algebraMap F ((w i).adicCompletion F) a - y i) ≤
      Valued.v (algebraMap F ((w i).adicCompletion F) c) :=
  GlobalTheory.T.exists_approx_finite_places_numberField w hw y c hc

theorem matrix_approx {ι : Type} [Fintype ι] [DecidableEq ι] (W Q : ι → Type) [∀ q, CommRing (W q)] [∀ q, IsDomain (W q)]
    [∀ q, IsDiscreteValuationRing (W q)] [∀ q, Field (Q q)] [∀ q, Algebra (W q) (Q q)] [∀ q, IsFractionRing (W q) (Q q)]
    {F : Type} [Field F] (f : ∀ q, F →+* Q q) (π : ∀ q, W q) (hπ : ∀ q, Irreducible (π q)) (t : F)
    (ht : ∀ q, f q t = algebraMap (W q) (Q q) (π q))
    (hd : ∀ (y : ∀ q, W q) (N : ℕ), ∃ x : F, ∀ q, ∃ z : W q, f q x = algebraMap (W q) (Q q) (y q + π q ^ N * z))
    {n : ℕ} (g : ∀ q, Matrix (Fin n) (Fin n) (Q q)) (hg : ∀ q, IsUnit (g q).det) (q0 : ι) :
    ∃ (B : Matrix (Fin n) (Fin n) F) (u : Matrix (Fin n) (Fin n) (W q0)), IsUnit u.det ∧
      B.map (f q0) = g q0 * u.map (algebraMap (W q0) (Q q0)) ∧
      ∀ q, q ≠ q0 → ∀ c, (fun i => f q (B i c)) ∈ Formalism.MainNotions.G.colSpan (W q) (g q) :=
  GlobalTheory.T.exists_global_matrix_approximation_mod_integral W Q f π hπ t ht hd g hg q0

theorem colSpan_mul_le {R K : Type} [CommRing R] [Field K] [Algebra R K] {k : ℕ} (g : Matrix (Fin k) (Fin k) K)
    (u : Matrix (Fin k) (Fin k) R) :
    Formalism.MainNotions.G.colSpan R (g * u.map (algebraMap R K)) ≤ Formalism.MainNotions.G.colSpan R g := by
  rw [Formalism.MainNotions.G.colSpan, Submodule.span_le]
  rintro _ ⟨c, rfl⟩
  have : (fun i => (g * u.map (algebraMap R K)) i c) = ∑ j, u j c • fun i => g i j := by
    funext i
    simp [Matrix.mul_apply, Algebra.smul_def, mul_comm]
  change (fun i => (g * u.map (algebraMap R K)) i c) ∈ Formalism.MainNotions.G.colSpan R g
  rw [this]
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

theorem colSpan_mul_eq {R K : Type} [CommRing R] [Field K] [Algebra R K] {k : ℕ} (g : Matrix (Fin k) (Fin k) K)
    (u : Matrix (Fin k) (Fin k) R) (hu : IsUnit u.det) :
    Formalism.MainNotions.G.colSpan R (g * u.map (algebraMap R K)) = Formalism.MainNotions.G.colSpan R g := by
  refine le_antisymm (colSpan_mul_le g u) ?_
  have := colSpan_mul_le (g * u.map (algebraMap R K)) u⁻¹
  rwa [Matrix.mul_assoc, ← Matrix.map_mul, Matrix.mul_nonsing_inv _ hu,
    Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one] at this

theorem map_int {F E : Type} [Field F] [NumberField F] [Field E] (w : HeightOneSpectrum (𝓞 F))
    (φ : E →+* w.adicCompletion F) (x : 𝓞 E) : φ x ∈ w.adicCompletionIntegers F := by
  have h2 : IsIntegral (w.adicCompletionIntegers F) (φ x) :=
    IsIntegral.map_of_comp_eq (Int.castRingHom _) φ (RingHom.ext_int _ _) x.isIntegral_coe
  obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := w.adicCompletionIntegers F)
    (K := w.adicCompletion F)).1 h2
  rw [← hy]
  exact y.2

theorem step {F : Type} [Field F] [NumberField F] (w : HeightOneSpectrum (𝓞 F)) {W Q : Type} [CommRing W] [Field Q]
    [Algebra W Q] (e : Q ≃+* w.adicCompletion F)
    (heW : ∀ x, x ∈ Set.range (algebraMap W Q) ↔ e x ∈ w.adicCompletionIntegers F) (p N : ℕ) (hp : (p : F) ≠ 0)
    (a : F) (y : W)
    (hv : Valued.v (algebraMap F (w.adicCompletion F) a - e (algebraMap W Q y)) ≤
      Valued.v (algebraMap F (w.adicCompletion F) ((p : F) ^ N))) :
    ∃ z : W, e.symm (algebraMap F (w.adicCompletion F) a) = algebraMap W Q (y + (p : W) ^ N * z) := by
  have hcc0 : algebraMap F (w.adicCompletion F) ((p : F) ^ N) ≠ 0 := (map_ne_zero _).2 (pow_ne_zero _ hp)
  have hz' : (algebraMap F (w.adicCompletion F) a - e (algebraMap W Q y)) / algebraMap F (w.adicCompletion F) ((p : F) ^ N) ∈
      w.adicCompletionIntegers F := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_div₀]
    exact div_le_one_of_le₀ hv zero_le
  obtain ⟨z, hz⟩ := (heW (e.symm _)).2 (by rw [e.apply_symm_apply]; exact hz')
  refine ⟨z, ?_⟩
  apply e.injective
  rw [e.apply_symm_apply, map_add, map_add, map_mul, hz, map_mul, e.apply_symm_apply, map_pow, map_pow, map_natCast,
    map_natCast]
  have hcc' : algebraMap F (w.adicCompletion F) ((p : F) ^ N) = (p : w.adicCompletion F) ^ N := by
    rw [map_pow, map_natCast]
  rw [← hcc', mul_div_cancel₀ _ hcc0]
  ring

variable {D : D7} {H : Formalism.L2.Herm.HermColsCh D} (Gs : Formalism.L2.Herm.SymmetricGroupCompatibility D H) (u : D.what₂.Word) (v : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar v))

theorem splitPlaceEmbedding_integers_mem_localIntegers (q : Fin (D.gat u v hg).P.nV) (r : 𝓞 D.host.E) :
    KerOne.iw0 Gs u v hg q (algebraMap (𝓞 D.host.E) D.host.E r) ∈
      Set.range (algebraMap ((D.gat u v hg).P.W q) ((D.gat u v hg).P.Qq q)) := by
  refine ((Gs u v hg).completion_integers_iff q _ rfl _).2 ?_
  rw [KerOne.splitPlaceIdempotent_cmEmbedding_compat]
  exact map_int _ (((RingHom.fst _ _).comp ((Gs u v hg).spl _ ((Gs u v hg).pl q).2).toRingHom).comp
      (Formalism.UG.inclE (F := D.host.F) ((((Gs u v hg).pl q).1).adicCompletion D.host.F))) r

theorem splitPlaceEmbedding_baseField_eq_completion (q : Fin (D.gat u v hg).P.nV) (a : D.host.F) :
    KerOne.iw0 Gs u v hg q (algebraMap D.host.F D.host.E a) =
      ((Gs u v hg).eQ q _ rfl).symm (algebraMap D.host.F ((((Gs u v hg).pl q).1).adicCompletion D.host.F) a) := by
  apply ((Gs u v hg).eQ q _ rfl).injective
  rw [KerOne.splitPlaceIdempotent_cmEmbedding_compat]
  refine ((Gs u v hg).spl_F _ _ a).trans ?_
  exact (RingEquiv.apply_symm_apply _ _).symm

theorem pl_inj : Function.Injective (fun q : Fin (D.gat u v hg).P.nV => ((Gs u v hg).pl q).1) :=
  fun _ _ h => (Gs u v hg).pl.injective (Subtype.ext h)

theorem dense (y : ∀ q, (D.gat u v hg).P.W q) (N : ℕ) : ∃ x : D.host.F, ∀ q, ∃ z : (D.gat u v hg).P.W q,
    KerOne.iw0 Gs u v hg q (algebraMap D.host.F D.host.E x) =
      algebraMap ((D.gat u v hg).P.W q) ((D.gat u v hg).P.Qq q)
        (y q + ((D.what₂.places.resChar v : ℕ) : (D.gat u v hg).P.W q) ^ N * z) := by
  rcases isEmpty_or_nonempty (Fin (D.gat u v hg).P.nV) with h | ⟨⟨q1⟩⟩
  · exact ⟨0, fun q => (IsEmpty.false q).elim⟩
  have hp0 : ((D.what₂.places.resChar v : ℕ) : D.host.F) ≠ 0 :=
    Nat.cast_ne_zero.2 (((D.gat u v hg).P.setting q1).prime.ne_zero)
  obtain ⟨a, ha⟩ := weak_approx (fun q => ((Gs u v hg).pl q).1) (pl_inj Gs u v hg)
    (fun q => (Gs u v hg).eQ q _ rfl (algebraMap ((D.gat u v hg).P.W q) ((D.gat u v hg).P.Qq q) (y q)))
    (((D.what₂.places.resChar v : ℕ) : D.host.F) ^ N) (pow_ne_zero _ hp0)
  refine ⟨a, fun q => ?_⟩
  obtain ⟨z, hz⟩ := step _ ((Gs u v hg).eQ q _ rfl) ((Gs u v hg).completion_integers_iff q _ rfl) _ N hp0 a (y q) (ha q)
  exact ⟨z, (splitPlaceEmbedding_baseField_eq_completion Gs u v hg q a).trans hz⟩

theorem exists_global_lattice (n : ℕ)
    (L : ∀ q : Fin (D.gat u v hg).P.nV, Submodule ((D.gat u v hg).P.W q) (Fin n → (D.gat u v hg).P.Qq q)) :
    (∀ q, G.IsLattice ((D.gat u v hg).P.W q) (L q)) →
    ∃ Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E), ∀ q,
      L q = Submodule.span ((D.gat u v hg).P.W q) {y | ∃ x ∈ Λ, y = fun i => KerOne.iw0 Gs u v hg q (x i)} := by
  intro hL
  choose g hgu hgL using hL
  have hfr : ∀ q, IsFractionRing ((D.gat u v hg).P.W q) ((D.gat u v hg).P.Qq q) :=
    fun q => ((D.gat u v hg).P.setting q).frac_alt
  let Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E) :=
    { carrier := {x | ∀ q, (fun i => KerOne.iw0 Gs u v hg q (x i)) ∈ L q}
      add_mem' := fun {x y} hx hy q => by
        have : (fun i => KerOne.iw0 Gs u v hg q ((x + y) i)) =
            (fun i => KerOne.iw0 Gs u v hg q (x i)) + fun i => KerOne.iw0 Gs u v hg q (y i) := by
          funext i; simp
        rw [this]; exact (L q).add_mem (hx q) (hy q)
      zero_mem' := fun q => by
        have : (fun i => KerOne.iw0 Gs u v hg q ((0 : Fin n → D.host.E) i)) = 0 := by funext i; simp
        rw [this]; exact (L q).zero_mem
      smul_mem' := fun r x hx q => by
        obtain ⟨c, hc⟩ := splitPlaceEmbedding_integers_mem_localIntegers Gs u v hg q r
        have : (fun i => KerOne.iw0 Gs u v hg q ((r • x) i)) = c • fun i => KerOne.iw0 Gs u v hg q (x i) := by
          funext i
          rw [Pi.smul_apply, Pi.smul_apply, Algebra.smul_def, map_mul, ← hc, Algebra.smul_def]
        rw [this]; exact (L q).smul_mem c (hx q) }
  refine ⟨Λ, fun q0 => ?_⟩
  obtain ⟨B, w, hw, hB, hoff⟩ := matrix_approx (fun q => (D.gat u v hg).P.W q) (fun q => (D.gat u v hg).P.Qq q)
    (fun q => (KerOne.iw0 Gs u v hg q).comp (algebraMap D.host.F D.host.E))
    (fun q => ((D.what₂.places.resChar v : ℕ) : (D.gat u v hg).P.W q)) (fun q => ((D.gat u v hg).P.setting q).p_unif)
    ((D.what₂.places.resChar v : ℕ) : D.host.F) (fun q => by rw [map_natCast, map_natCast])
    (fun y N => dense Gs u v hg y N) g hgu q0
  have hcol : ∀ c, (fun i => algebraMap D.host.F D.host.E (B i c)) ∈ Λ := by
    intro c q
    by_cases hq : q = q0
    · subst hq
      have : (fun i => KerOne.iw0 Gs u v hg q (algebraMap D.host.F D.host.E (B i c))) =
          fun i => (g q * w.map (algebraMap ((D.gat u v hg).P.W q) ((D.gat u v hg).P.Qq q))) i c := by
        funext i; exact congrFun (congrFun hB i) c
      show (fun i => KerOne.iw0 Gs u v hg q (algebraMap D.host.F D.host.E (B i c))) ∈ L q
      rw [this, hgL q, ← colSpan_mul_eq (g q) w hw]
      exact Submodule.subset_span ⟨c, rfl⟩
    · show (fun i => KerOne.iw0 Gs u v hg q (algebraMap D.host.F D.host.E (B i c))) ∈ L q
      rw [hgL q]; exact hoff q hq c
  apply le_antisymm
  · rw [hgL q0, ← colSpan_mul_eq (g q0) w hw, Formalism.MainNotions.G.colSpan, Submodule.span_le]
    rintro _ ⟨c, rfl⟩
    refine Submodule.subset_span ⟨_, hcol c, ?_⟩
    funext i; exact (congrFun (congrFun hB i) c).symm
  · rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    exact hx q0

end GlobalTheory.Mem.Top.KerGlob
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsInertHeckeDoubleCosetOperatorsLifts
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
set_option maxHeartbeats 1000000

noncomputable section

namespace GlobalTheory.Mem.R3.LiftBrg.InertTie

theorem conj_symm_apply {K M N : Type} [CommSemiring K] [AddCommMonoid M] [Module K M] [AddCommMonoid N] [Module K N]
    (e : M ≃ₗ[K] N) (T : Module.End K M) (x : N) : e.symm (e.conj T x) = T (e.symm x) := by
  simp [LinearEquiv.conj_apply]

theorem opEq (X : Stages) {px : PreX X.B.toPre} (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι)
    (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U))
    (cV : ∀ i, CoefA (Vc X.toD7 i)) (i : Fin X.toD7.R.m) (t : TupU I U) (A k : GL (Fin X.B.R.nV) (LiftBrg.EA X))
    (P : LiftBrg.PresL X I hX U Xg tr L cV i t) (hP : LiftBrg.ReadsStd X I hX U Xg tr L cV i t A k P)
    (q : ↑((famR X I hX U Xg tr).okI t) × List ℕ) (R : Finset (Bridge.Gf (Vc X.toD7 i)))
    (hN : ∀ (M : Type) [AddCommMonoid M] (ψ : Formalism.L2.Col.DecoSet X.toD7.host.E X.B.R.nV ∅ (LiftBrg.sgL X I U t) → M)
        (g : Bridge.Gf (Vc X.toD7 i)),
        ∑ a ∈ R, ψ (LiftBrg.ptL X I U i t A k (g * a)) =
          ∑ e ∈ (LiftBrg.ptL X I U i t A k g).inertNb ((q.1.1 : PlI X.B px).1).asIdeal q.2, ψ e)
    (f : ((famR X I hX U Xg tr).A.MtCSD i t).Forms) :
    P.ext ((((famR X I hX U Xg tr).heckeLI i t q f : ((famR X I hX U Xg tr).A.MtCSD i t).Forms) :
        ((famR X I hX U Xg tr).A.MtCSD i t).Cl → ((famR X I hX U Xg tr).A.MtCSD i t).V)) =
      Bridge.dcOp R (P.ext (f : ((famR X I hX U Xg tr).A.MtCSD i t).Cl → ((famR X I hX U Xg tr).A.MtCSD i t).V)) := by
  funext g
  rw [hP]
  unfold Bridge.dcOp
  rw [Finset.sum_congr rfl (fun a _ => hP f (g * a))]
  rw [hN _ (fun e => P.coef ((((Formalism.L2.Col.mtKGSD X.B.wts I.Ch I.sel t.1 ((i : ℕ) + 1)).res
        (Formalism.L2.Col.mtKOk X.B.wts I.Ch I.sel t.1 hX ((i : ℕ) + 1))).symm f).1 e)) g]
  refine (congrArg P.coef ?_).trans (map_sum P.coef _ _)
  change (((Formalism.L2.Col.mtKGSD X.B.wts I.Ch I.sel t.1 ((i : ℕ) + 1)).res
        (Formalism.L2.Col.mtKOk X.B.wts I.Ch I.sel t.1 hX ((i : ℕ) + 1))).symm
        (((Formalism.L2.Col.mtKGSD X.B.wts I.Ch I.sel t.1 ((i : ℕ) + 1)).res
        (Formalism.L2.Col.mtKOk X.B.wts I.Ch I.sel t.1 hX ((i : ℕ) + 1))).conj
        (Formalism.L2.Col.heckeFamI (formPts _ _) ∅ (offSubI.lev q.1, q.2)) f)).1 _ = _
  erw [conj_symm_apply]
  erw [Formalism.L2.Col.heckeI_op_apply]
  unfold Formalism.L2.Col.DecoPts.nbI
  simp [formPts]
  rfl

theorem exists_inertTie : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r), I.Ok → ValsIn I → LevOf X I U L → IsPlacewiseIdentity X (px := px) eG → ∀ (cV : ∀ i, CoefA (Vc X.toD7 i)) (i : Fin X.toD7.R.m) (t : TupU I U) (A k : GL (Fin X.B.R.nV) (LiftBrg.EA X)), LiftBrg.FrameOK X I U i t A k → ∀ P : LiftBrg.PresL X I hX U Xg tr L cV i t, LiftBrg.ReadsStd X I hX U Xg tr L cV i t A k P →
    Nonempty (Bridge.HeckeTie (Bridge.ratF (Vc X.toD7 i)) P ((famR X I hX U Xg tr).heckeLI i t)
      (fun k => Formalism.L2.Col.InertTypeOk (Vc X.toD7 i).rank k.2)
      (fun k => IsLabElt (Vc X.toD7 i) (k.1.1 : PlI X.B px).1 (labIn (Vc X.toD7 i).rank k.2))
      fun k => IsLocElt (Vc X.toD7 i) (k.1.1 : PlI X.B px).1) := by
  intro X px I hX U Xg tr L eG hI hV hL hG cV i t A k hF P hR
  classical
  have hN := fun (q : ↑((famR X I hX U Xg tr).okI t) × List ℕ)
      (hq : Formalism.L2.Col.InertTypeOk (Vc X.toD7 i).rank q.2) =>
    GlobalTheory.T.inertNeighbours_lifts_doubleCoset_translates X px I hX U Xg tr L eG hI hV hL hG cV i t A k hF q hq
  exact ⟨{
    hx := fun q => if hq : Formalism.L2.Col.InertTypeOk (Vc X.toD7 i).rank q.2 then (hN q hq).choose else 1
    hA := fun q => if hq : Formalism.L2.Col.InertTypeOk (Vc X.toD7 i).rank q.2 then (hN q hq).choose_spec.choose else ∅
    hx_ok := fun q hq => by
      simp only [dif_pos hq]
      exact (hN q hq).choose_spec.choose_spec.1
    hA_loc := fun q hq => by
      simp only [dif_pos hq]
      exact (hN q hq).choose_spec.choose_spec.2.1
    chi_loc := fun q _ j hj => GlobalTheory.T.levelChar_eq_one_inert_prime_off_level X px I hX U Xg tr L eG hI hV hL hG cV i t q j hj
    hDC := fun q hq => by
      simp only [dif_pos hq]
      exact (hN q hq).choose_spec.choose_spec.2.2.1
    op_eq := fun q hq f => by
      simp only [dif_pos hq]
      exact opEq X I hX U Xg tr L cV i t A k P hR q _ (hN q hq).choose_spec.choose_spec.2.2.2 f }⟩

end GlobalTheory.Mem.R3.LiftBrg.InertTie
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocalCoefficientFieldEmbeddingKernelPlace
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.KerIK

open Cardinal

theorem kf_hom_of_isRec {sc : Scale} {D : D7} {Gt : GatTies D} {c : LatCmp D} {H : Formalism.L2.Herm.Herm0 D}
    {F : ∀ u, Formalism.L2.Forms.Forms0 D u} (h : IsRecG sc D Gt c H F) (u : D.what₂.Word) (v : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar v)) [Fact (D.what₂.places.resChar v).Prime] :
    Nonempty ((D.gat u v hg).Kf →+* ℂ_[D.what₂.places.resChar v]) := by
  obtain ⟨D0, Lc, I, ψ, hd, H0, hL, T, B, hBs, hB, iK, lam, hK, hPos, CH, eq⟩ := h
  cases eq
  exact ⟨iK u v hg⟩

theorem mk_LL_le (D : D7) : #D.what₂.LL ≤ ℵ₀ := by
  have := Algebra.IsAlgebraic.cardinalMk_le_max ℚ D.what₂.LL
  rwa [Cardinal.mkRat, max_self] at this

theorem exists_iK : ∀ {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T), K.Over B.toPre → Forced K B T → Pinned K B f T w →
    ∀ (Z : w.Lt) (t : ColumnDataSplitPrimes K w Z) (Wt : Set B.places.Pl) (nch : NChoice (w.D Z)) (_ : NchT w Z Wt nch) (Y : DivX (w.D Z)),
    V4.MuIsW (w.st Z) f T Wt w.I.xi → TC.QpIs w.I Y.Qp →
    ∀ (O : ∀ u a, GL3Theta.LiftObj (w.D Z) ((w.D Z).chTw u a)), TC.StdO w.I w.l Z Y.Qp O →
    (∀ u a i, i < B.R.m → Formalism.L2.Ker.UnfIsAll (O u a) i) → ∀ (E : KerEnt (w.D Z) Y (w.tw Z)), TC.EntOk E O →
    ∀ u (v : (w.D Z).what₂.places.Pl) (hg : GIdx (w.D Z).host ((w.D Z).mem u).A.T ((w.D Z).what₂.places.resChar v)),
      haveI : Fact ((w.D Z).what₂.places.resChar v).Prime := ⟨(w.D Z).what₂.places.resChar_prime v⟩
      ∃ iK : ((w.D Z).gat u v hg).Kf →+* ℂ_[(w.D Z).what₂.places.resChar v],
        ∀ (x : (w.D Z).what₂.LL) (hx : (w.D Z).what₂.embLL x ∈ algebraicClosure ℚ ℂ),
          iK (t.cmp.embW u v hg x) = E.lam v ⟨(w.D Z).what₂.embLL x, hx⟩ := by
  intro K B f T w _ _ _ Z t Wt nch _ Y _ _ O _ _ E _ u v hg
  haveI : Fact ((w.D Z).what₂.places.resChar v).Prime := ⟨(w.D Z).what₂.places.resChar_prime v⟩
  obtain ⟨i0⟩ := kf_hom_of_isRec t.isRec u v hg
  have hC : ℵ₀ < #ℂ_[(w.D Z).what₂.places.resChar v] :=
    Cardinal.aleph0_lt_continuum.trans_le (continuum_le_cardinal_of_nontriviallyNormedField _)
  obtain ⟨σ, hσ⟩ := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.extEmb_equiv_comp (i0.comp (t.cmp.embW u v hg)) (E.iL v)
    (mk_LL_le (w.D Z)) hC rfl
  refine ⟨σ.toRingHom.comp i0, fun x hx => ?_⟩
  have h1 := hσ x
  have h2 := E.iL_lam v x
  simp only [RingHom.comp_apply] at h1
  simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
  rw [h1, h2, lamV, dif_pos hx]

end GlobalTheory.KerIK
end
end

