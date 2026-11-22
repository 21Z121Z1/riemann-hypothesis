import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0092
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OperatorRepresentations
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0093
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0094

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTRTopActCut
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.TopAct

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def QTop : Prop :=
  ∀ (A : Type) [Ring A] [Algebra ℂ A] (n : ℕ) (E : Fin n → Fin n → A) (h : ℂ),
    ∃ d : ℕ → A, (∀ Y : ℂ, qminor E id id (Y + h) = ∑ j ∈ Finset.range (n + 1), Y ^ j • d j) ∧
      (1 ≤ n → d (n - 1) = ∑ a, E a a + algebraMap ℂ A ((n : ℂ) * h - (n : ℂ) * ((n : ℂ) - 1) / 2))

theorem interp {V : Type*} [AddCommGroup V] [Module ℂ V] (N : ℕ) (W : Matrix (Fin N) (Fin N) ℂ)
    (hW : W * Matrix.vandermonde (fun i : Fin N => ((i : ℕ) : ℂ)) = 1) (p : ℂ → V) (a : ℕ → V)
    (ha : ∀ Y, p Y = ∑ j ∈ Finset.range N, Y ^ j • a j) (j : Fin N) :
    ∑ i : Fin N, W j i • p ((i : ℕ) : ℂ) = a j := by
  have key : ∀ l : Fin N, ∑ i : Fin N, W j i * ((i : ℕ) : ℂ) ^ (l : ℕ) = if j = l then 1 else 0 := by
    intro l
    have h := congrFun (congrFun hW j) l
    simpa [Matrix.mul_apply, Matrix.vandermonde_apply, Matrix.one_apply] using h
  simp_rw [ha, Finset.sum_range, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul, key, ite_smul, one_smul, zero_smul]
  simp

theorem vdm_inv (N : ℕ) : ∃ W : Matrix (Fin N) (Fin N) ℂ,
    W * Matrix.vandermonde (fun i : Fin N => ((i : ℕ) : ℂ)) = 1 := by
  refine ⟨(Matrix.vandermonde (fun i : Fin N => ((i : ℕ) : ℂ)))⁻¹, Matrix.nonsing_inv_mul _ ?_⟩
  rw [isUnit_iff_ne_zero, Matrix.det_vandermonde_ne_zero_iff]
  intro a b h
  exact Fin.ext (Nat.cast_injective h)

theorem pt_poly (hQ : QTop) {k r : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (D : Set (Mx k r)) (hD : IsOpen D) (f : Mx k r → V) (hf : SmoothLev k r (Fin.last r) D f)
    {g : Mx k r} (hg : g ∈ Glev k r (Fin.last r) ∩ D) :
    ∃ a : ℕ → V, (∀ Y : ℂ, capL k r (Fin.last r) (uC k r (Fin.last r) Y) f g =
        ∑ j ∈ Finset.range (mdim k r (Fin.last r) + 1), Y ^ j • a j) ∧
      a (mdim k r (Fin.last r) - 1) = ∑ b : Fin (mdim k r (Fin.last r)),
        EH k r (posL k r (Fin.last r) b) (posL k r (Fin.last r) b) f g := by
  obtain ⟨d, hd, htop⟩ := hQ (Module.End ℂ (SV k r (Fin.last r) D V)) (mdim k r (Fin.last r))
    (EV k r (Fin.last r) D V) (((mdim k r (Fin.last r) : ℂ) - 1) / 2)
  refine ⟨fun j => (d j (mkV hD f hf)).1 g, fun Y => ?_, ?_⟩
  · have h1 := (OperatorRepresentations.rep_qminor (E := V) hD (id : Fin (mdim k r (Fin.last r)) → Fin (mdim k r (Fin.last r))) id
      (uC k r (Fin.last r) Y)).mkV hD hf hg
    simp only [Function.comp_id] at h1
    have e : uC k r (Fin.last r) Y = Y + ((mdim k r (Fin.last r) : ℂ) - 1) / 2 := rfl
    unfold capL
    rw [← h1, e, hd Y, LinearMap.sum_apply, Submodule.coe_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [LinearMap.smul_apply, Submodule.coe_smul, Pi.smul_apply]
  · have hn1 : 1 ≤ mdim k r (Fin.last r) := by simp [mdim]
    show (d (mdim k r (Fin.last r) - 1) (mkV hD f hf)).1 g = _
    rw [htop hn1]
    have e0 : ((mdim k r (Fin.last r) : ℂ) * (((mdim k r (Fin.last r) : ℂ) - 1) / 2) -
        (mdim k r (Fin.last r) : ℂ) * ((mdim k r (Fin.last r) : ℂ) - 1) / 2) = 0 := by ring
    rw [e0, map_zero, add_zero, LinearMap.sum_apply, Submodule.coe_sum, Finset.sum_apply]
    exact Finset.sum_congr rfl fun b _ => (OperatorRepresentations.rep_EV (E := V) hD b b).mkV hD hf hg

theorem mdim_last (k r : ℕ) : mdim k r (Fin.last r) = k + 1 := by
  simp [Q.mdim]

theorem gTRTopAct_of_cut (hQ : QTop) : GTRTopAct := by
  intro Wp Wq _ _ _ _ _ _ P z z' π π' hpl hk X
  obtain ⟨W, hW⟩ := vdm_inv (P.k + 2)

  have hpt : ∀ (Φ : RadSp P.k P.r z z' π π'), ∀ x ∈ DomR P.k P.r z z',
      ∃ a : ℕ → (Wq →L[ℂ] Wp), (∀ Y : ℂ, ((X.t Y 0 0 Φ : RadSp P.k P.r z z' π π') : Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2 =
          ∑ j ∈ Finset.range (P.k + 2), Y ^ j • a j) ∧
        a P.k = ∑ b : Fin (mdim P.k P.r (Fin.last P.r)),
          EH P.k P.r (posL P.k P.r (Fin.last P.r) b) (posL P.k P.r (Fin.last P.r) b)
            ((Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) x.1) x.2 := by
    intro Φ x hx
    have hmem := Φ.2
    obtain ⟨_, hs, _⟩ := hmem
    obtain ⟨U, F, hU, hxU, hF, hΦ⟩ := hs x hx
    set D : Set (Mx P.k P.r) := {g | (x.1, g) ∈ U} with hDdef
    have hc : ContDiff ℝ ∞ (fun g : Mx P.k P.r => (x.1, g)) := contDiff_prodMk_right x.1
    have hD : IsOpen D := hU.preimage hc.continuous
    have hf : SmoothLev P.k P.r (Fin.last P.r) D ((Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) x.1) := by
      intro g₀ hg₀
      refine ⟨D, fun g => F (x.1, g), hD, hg₀.2, ?_, fun g hgD hgG => hΦ (x.1, g) hgD hgG⟩
      exact hF.comp hc.contDiffOn (fun g hg => hg)
    have hg : x.2 ∈ Glev P.k P.r (Fin.last P.r) ∩ D := ⟨hx.2.1, by simpa [hDdef] using hxU⟩
    obtain ⟨a, ha, htop⟩ := pt_poly hQ D hD _ hf hg
    have hm : mdim P.k P.r (Fin.last P.r) + 1 = P.k + 2 := by rw [mdim_last]
    have hm1 : mdim P.k P.r (Fin.last P.r) - 1 = P.k := by rw [mdim_last]; rfl
    refine ⟨a, fun Y => ?_, ?_⟩
    · rw [X.t_apply Y 0 0 Φ x hx, ← hm]
      exact ha Y
    · rw [← htop, hm1]

  let c : ℕ → Module.End ℂ (RadSp P.k P.r z z' π π') := fun j =>
    if h : j < P.k + 2 then ∑ i : Fin (P.k + 2), W ⟨j, h⟩ i • X.t ((i : ℕ) : ℂ) 0 0 else 0
  have hval : ∀ (T : Module.End ℂ (RadSp P.k P.r z z' π π')) (Φ : RadSp P.k P.r z z' π π') x,
      x ∉ DomR P.k P.r z z' → ((T Φ : RadSp P.k P.r z z' π π') : Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2 = 0 := by
    intro T Φ x hx
    have hmem := (T Φ).2
    obtain ⟨h0, _, _⟩ := hmem
    exact h0 x hx
  have hc : ∀ (Φ : RadSp P.k P.r z z' π π'), ∀ x ∈ DomR P.k P.r z z', ∀ (a : ℕ → (Wq →L[ℂ] Wp)),
      (∀ Y : ℂ, ((X.t Y 0 0 Φ : RadSp P.k P.r z z' π π') : Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2 =
          ∑ j ∈ Finset.range (P.k + 2), Y ^ j • a j) →
      ∀ j ∈ Finset.range (P.k + 2), ((c j Φ : RadSp P.k P.r z z' π π') : Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2 = a j := by
    intro Φ x hx a ha j hj
    have hj' : j < P.k + 2 := Finset.mem_range.1 hj
    have e1 : c j = ∑ i : Fin (P.k + 2), W ⟨j, hj'⟩ i • X.t ((i : ℕ) : ℂ) 0 0 := dif_pos hj'
    rw [e1, LinearMap.sum_apply, Submodule.coe_sum, Finset.sum_apply, Finset.sum_apply]
    simp only [LinearMap.smul_apply, Submodule.coe_smul, Pi.smul_apply]
    exact interp (P.k + 2) W hW (fun Y => ((X.t Y 0 0 Φ : RadSp P.k P.r z z' π π') : Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2)
      a ha ⟨j, hj'⟩
  refine ⟨c, fun Y => ?_, 0, fun Φ x hx => ?_⟩
  · apply LinearMap.ext
    intro Φ
    apply Subtype.ext
    funext c0 g
    by_cases hx : (c0, g) ∈ DomR P.k P.r z z'
    · obtain ⟨a, ha, -⟩ := hpt Φ (c0, g) hx
      have hL := ha Y
      simp only at hL
      rw [hL, LinearMap.sum_apply, Submodule.coe_sum, Finset.sum_apply, Finset.sum_apply]
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [LinearMap.smul_apply, Submodule.coe_smul, Pi.smul_apply, Pi.smul_apply]
      congr 1
      exact (hc Φ (c0, g) hx a ha j hj).symm
    · have h1 := hval (X.t Y 0 0) Φ (c0, g) hx
      have h2 := hval (∑ j ∈ Finset.range (P.k + 2), Y ^ j • c j) Φ (c0, g) hx
      simp only at h1 h2
      rw [h1, h2]
  · obtain ⟨a, ha, htop⟩ := hpt Φ x hx
    rw [hc Φ x hx a ha P.k (Finset.mem_range.2 (by omega)), htop]
    simp

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.TopAct
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPRhoCapSmooth
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Filter Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.JA.PRhoCut

open Formalism.FourierDecayAlt.P

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace CapSm

variable {k r : ℕ} {Wp : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [FiniteDimensional ℂ Wp]

def glW (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (hπ : Qr.IsRepW k r z π) :
    Submodule ℂ (Mx k r) where
  carrier := {Z | Qr.InGlW k r z Z}
  add_mem' := fun {Z Z'} hZ hZ' => (elementary_lie_elements Wp k r z π hπ Z Z' hZ hZ').1.1
  zero_mem' := by
    have h := LieListProducts.gl_comb (LieListProducts.lie_zero (k := k) (r := r) (z := z)) (LieListProducts.lie_zero (k := k) (r := r) (z := z))
    simpa using h
  smul_mem' := fun c Z hZ => ((elementary_lie_elements Wp k r z π hπ Z Z hZ hZ).2.1 c).1

def ecL (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (hπ : Qr.IsRepW k r z π) :
    glW k r z π hπ →ₗ[ℂ] (Wp →L[ℂ] Wp) where
  toFun Z := QrD.ecOp π Z.1
  map_add' Z Z' := (elementary_lie_elements Wp k r z π hπ Z.1 Z'.1 Z.2 Z'.2).1.2
  map_smul' c Z := ((elementary_lie_elements Wp k r z π hπ Z.1 Z.1 Z.2 Z.2).2.1 c).2

theorem foldr_apply (l : List (Wp →L[ℂ] Wp)) (v : Wp) :
    List.foldr (fun (T : Wp → Wp) h => T h) v (List.map (fun T : Wp →L[ℂ] Wp => (⇑T : Wp → Wp)) l) =
      (l.foldr (fun (T acc : Wp →L[ℂ] Wp) => T.comp acc) 1) v := by
  induction l with
  | nil => simp
  | cons T l ih =>
    simp only [List.map_cons, List.foldr_cons, ContinuousLinearMap.comp_apply, ih]

theorem foldr_contDiff {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] (l : List (X → (Wp →L[ℂ] Wp)))
    (h : ∀ f ∈ l, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => (l.map fun f => f x).foldr (fun (T acc : Wp →L[ℂ] Wp) => T.comp acc) 1) := by
  have hc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : (Wp →L[ℂ] Wp) × (Wp →L[ℂ] Wp) => p.1.comp p.2) :=
    (isBoundedBilinearMap_comp (𝕜 := ℂ) (E := Wp) (F := Wp) (G := Wp)).contDiff.restrict_scalars ℝ
  induction l with
  | nil => simpa using contDiff_const
  | cons f l ih =>
    have hf := h f (List.mem_cons_self ..)
    have hl := ih fun g hg => h g (List.mem_cons_of_mem _ hg)
    simp only [List.map_cons, List.foldr_cons]
    exact hc.comp (hf.prodMk hl)

theorem unitB_contDiff {m : ℕ} (a b : Fin m) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun Bs : Fin m → Fin (2 * r + k + 1) → ℂ => unitB (Hpk k r) Bs a b) := by
  unfold unitB
  refine contDiff_pi.2 fun p => contDiff_pi.2 fun q => ?_
  simp only [Matrix.of_apply, herm, dotProduct, Pi.star_apply]
  refine ContDiff.mul (contDiff_apply_apply ℝ ℂ a p) (ContDiff.sum fun i _ => ?_)
  exact (Complex.conjCLE.contDiff.comp (contDiff_apply_apply ℝ ℂ b i)).mul contDiff_const

end CapSm

open CapSm in
theorem capacity_smoothness_holds : CapSmooth := by
  intro Wp _ _ _ k r m z π hπ w
  obtain ⟨G', hG'⟩ := Submodule.exists_isCompl (glW k r z π hπ)
  let Lext : Mx k r →ₗ[ℂ] (Wp →L[ℂ] Wp) := (ecL z π hπ).comp (Submodule.linearProjOfIsCompl _ _ hG')
  have hLext : ∀ Z (hZ : Qr.InGlW k r z Z), Lext Z = QrD.ecOp π Z := by
    intro Z hZ
    have hmem : Z ∈ glW k r z π hπ := hZ
    have e := Submodule.linearProjOfIsCompl_apply_left hG' ⟨Z, hmem⟩
    show ecL z π hπ (Submodule.linearProjOfIsCompl _ _ hG' Z) = _
    erw [e]
    rfl
  let Lc : Mx k r →L[ℂ] (Wp →L[ℂ] Wp) := LinearMap.toContinuousLinearMap Lext
  have hLc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun Z : Mx k r => Lc Z) := (Lc.restrictScalars ℝ).contDiff
  let T : Equiv.Perm (Fin m) → Fin m → (Fin m → Fin (2 * r + k + 1) → ℂ) → (Wp →L[ℂ] Wp) := fun σ t Bs =>
    (if σ t = t then (w - ((t : ℕ) : ℂ)) • (1 : Wp →L[ℂ] Wp) else 0) + Lc (unitB (Hpk k r) Bs (σ t) t)
  refine ⟨fun Bs => ∑ σ : Equiv.Perm (Fin m), (((Equiv.Perm.sign σ : ℤ) : ℂ)) •
    ((List.ofFn fun t => T σ t).map fun f => f Bs).foldr (fun (T acc : Wp →L[ℂ] Wp) => T.comp acc) 1, ?_, ?_⟩
  · refine ContDiff.sum fun σ _ => ContDiff.const_smul _ ?_
    refine foldr_contDiff _ fun f hf => ?_
    obtain ⟨t, rfl⟩ := List.mem_ofFn.1 hf
    exact contDiff_const.add (hLc.comp (unitB_contDiff _ _))
  · intro Bs hB v
    unfold capRep qmF
    rw [ContinuousLinearMap.sum_apply]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [ContinuousLinearMap.smul_apply, ← foldr_apply]
    congr 2
    simp only [List.map_ofFn]
    congr 1
    funext t y
    have hl := QrD.frame_lie hB (σ t) t
    have hgl : Qr.InGlW k r z (unitB (Hpk k r) Bs (σ t) t) := hl
    simp only [Function.comp_apply, T, id]
    rw [ContinuousLinearMap.add_apply, QrD.ecRep_eq hπ.1 hπ.2 hl.1 hl.2 (k := k) (r := r), ← hLext _ hgl]
    congr 1
    split_ifs <;> simp

end Formalism.FourierDecayAlt.P.CutMP.JA.PRhoCut
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPRhoEigOrth
section
open Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.JA.PRhoCut

open Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.JA

namespace EigenvectorOrthogonality

variable {k r : ℕ}

private theorem herm_mulVec_of_conjTranspose_mul_H_mul_eq {n : ℕ} {H g : Matrix (Fin n) (Fin n) ℂ} (hg : gᴴ * H * g = H)
    (v w : Fin n → ℂ) : herm H (g *ᵥ v) (g *ᵥ w) = herm H v w := by
  unfold herm
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec]
  simp only [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hg]

theorem frame_move {z e : Fin (2 * r + k + 1) → ℂ} {h : Mx k r} (hh : h ∈ UWset k r z) (he : h *ᵥ e = e) {m : ℕ}
    {F : Fin m → Fin (2 * r + k + 1) → ℂ} (hF : IsFrameOf k r [z, e] F) :
    IsFrameOf k r [z, e] (fun p => h *ᵥ F p) := by
  have hG : h ∈ Glev k r (Fin.last r) := ⟨hh.1, fun a _ => hh.2.1 a⟩
  have hU : hᴴ * Hpk k r * h = Hpk k r := hh.1
  refine ⟨fun a => (Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors.glev_inWb hG (hF.1 a)).1, fun a b => ?_, fun a v hv => ?_⟩
  · rw [herm_mulVec_of_conjTranspose_mul_H_mul_eq hU]
    exact hF.2.1 a b
  · have hv' : h *ᵥ v = v := by
      rcases List.mem_cons.1 hv with rfl | hv2
      · exact hh.2.2
      · rcases List.mem_cons.1 hv2 with rfl | hv3
        · exact he
        · simp at hv3
    calc herm (Hpk k r) (h *ᵥ F a) v = herm (Hpk k r) (h *ᵥ F a) (h *ᵥ v) := by rw [hv']
      _ = 0 := by rw [herm_mulVec_of_conjTranspose_mul_H_mul_eq hU]; exact hF.2.2 a v hv

theorem frame_swap {z e : Fin (2 * r + k + 1) → ℂ} {m : ℕ} {F : Fin m → Fin (2 * r + k + 1) → ℂ}
    (hF : IsFrameOf k r [z, e] F) : IsFrameOf k r [e, z] F :=
  ⟨hF.1, hF.2.1, fun a v hv => hF.2.2 a v (by simp only [List.mem_cons] at hv ⊢; tauto)⟩

private theorem isUnit_det_of_mem_UWset {h : Mx k r} {z : Fin (2 * r + k + 1) → ℂ} (hh : h ∈ UWset k r z) :
    IsUnit h.det := by
  have hU : hᴴ * Hpk k r * h = Hpk k r := hh.1
  have hH : (Hpk k r).det ≠ 0 := by
    have h1 := congrArg Matrix.det (Formalism.QuantumDeterminants.hpkFacts k r).2.1
    rw [Matrix.det_mul, Matrix.det_one] at h1
    intro h0
    rw [h0, zero_mul] at h1
    exact zero_ne_one h1
  have h2 := congrArg Matrix.det hU
  rw [Matrix.det_mul, Matrix.det_mul] at h2
  refine isUnit_iff_ne_zero.2 fun h0 => hH ?_
  rw [h0, mul_zero] at h2
  exact h2.symm

theorem mulVec_inv_cancel {h : Mx k r} {z : Fin (2 * r + k + 1) → ℂ} (hh : h ∈ UWset k r z) (v : Fin (2 * r + k + 1) → ℂ) :
    h *ᵥ (h⁻¹ *ᵥ v) = v := by
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_det_of_mem_UWset hh), Matrix.one_mulVec]

theorem inv_fix {h : Mx k r} {z e : Fin (2 * r + k + 1) → ℂ} (hh : h ∈ UWset k r z) (he : h *ᵥ e = e) :
    h⁻¹ *ᵥ e = e := by
  calc h⁻¹ *ᵥ e = h⁻¹ *ᵥ (h *ᵥ e) := by rw [he]
    _ = e := by rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (isUnit_det_of_mem_UWset hh), Matrix.one_mulVec]

end EigenvectorOrthogonality

open EigenvectorOrthogonality in
theorem eigenvector_orthogonality_holds : EigOrth := by
  intro Wp _ _ _ k r z e π hz hT hrep hunit hex f g x y hx hy hfg
  obtain ⟨Fr₀, hFr₀⟩ := hex
  obtain ⟨w₀, hw₀⟩ := hfg
  have hlin : ∀ Fr : Fin (k - 1) → Fin (2 * r + k + 1) → ℂ, IsFrameOf k r [z, e] Fr → ∀ w,
      P.Qx8.IsLin (capRep k r π Fr w) := fun Fr hFr w =>
    P.Qx8.capRep_lin hFr (by simp) hrep.1 hrep.2 w
  set S := K k r z e π g with hS

  have hmem : ∀ v ∈ S, v ∈ Kset k r z e π g := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem u hu => exact hu
    | zero =>
      intro Fr hFr w
      rw [(hlin Fr hFr w).map_zero, smul_zero]
    | add a b _ _ ha hb =>
      intro Fr hFr w
      rw [(hlin Fr hFr w).map_add, ha Fr hFr w, hb Fr hFr w, smul_add]
    | smul c a _ ha =>
      intro Fr hFr w
      rw [(hlin Fr hFr w).map_smul, ha Fr hFr w, smul_comm]

  have hmul : ∀ a ∈ UWset k r z, ∀ b ∈ UWset k r z, ∀ v, π (a * b) v = π a (π b v) := by
    intro a ha b hb v
    rw [hrep.1.2 a ha b hb]; rfl
  have hinv : ∀ h ∈ UWset k r z, ∀ v, π h (π h⁻¹ v) = v := by
    intro h hh v
    rw [← hmul h hh _ (WeylGroupFacts.uw_inv hh), Matrix.mul_nonsing_inv _ (WeylGroupFacts.isUnit_of_uh hh.1), hrep.1.1]; rfl
  have hstab : ∀ h ∈ UWset k r z, h *ᵥ e = e → ∀ v ∈ Kset k r z e π g, π h v ∈ Kset k r z e π g := by
    intro h hh he v hv Fr hFr w
    have hFr' : IsFrameOf k r [z, e] (fun p => h⁻¹ *ᵥ Fr p) := frame_move (WeylGroupFacts.uw_inv hh) (inv_fix hh he) hFr
    have key := P.Qx8.capRep_intertwine (frame_swap hFr') hrep.1 hrep.2 hh.1 (π h)
      (fun h' hh' _ v => by
        rw [← hmul h hh h' hh', ← hmul _ (WeylGroupFacts.uw_mul (WeylGroupFacts.uw_mul hh hh') (WeylGroupFacts.uw_inv hh)) h hh,
          Matrix.mul_assoc (h * h'), Matrix.nonsing_inv_mul _ (WeylGroupFacts.isUnit_of_uh hh.1), Matrix.mul_one]) w v
    simp only [mulVec_inv_cancel hh] at key
    rw [← key, hv _ hFr' w, map_smul]
  have hstabS : ∀ h ∈ UWset k r z, h *ᵥ e = e → ∀ v ∈ S, π h v ∈ S := fun h hh he v hv =>
    Submodule.subset_span (hstab h hh he v (hmem v hv))
  have hstabO : ∀ h ∈ UWset k r z, h *ᵥ e = e → ∀ u ∈ Sᗮ, π h u ∈ Sᗮ := by
    intro h hh he u hu s hs
    let L : Wp →ₗᵢ[ℂ] Wp := ⟨(π h : Wp →ₗ[ℂ] Wp), hunit h hh⟩
    have hs' : π h⁻¹ s ∈ S := hstabS _ (WeylGroupFacts.uw_inv hh) (inv_fix hh he) s hs
    have e2 : inner ℂ (π h (π h⁻¹ s)) (π h u) = inner ℂ (π h⁻¹ s) u := L.inner_map_map _ _
    rw [hinv h hh s] at e2
    rw [e2]
    exact Submodule.inner_right_of_mem_orthogonal hs' hu
  have hcomm : ∀ h ∈ UWset k r z, h *ᵥ e = e → ∀ v, S.starProjection (π h v) = π h (S.starProjection v) := by
    intro h hh he v
    refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero (hstabS h hh he _ (S.starProjection_apply_mem v)) ?_
    intro s hs
    have : π h v - π h (S.starProjection v) = π h (v - S.starProjection v) := by rw [map_sub]
    rw [this]
    exact Submodule.inner_left_of_mem_orthogonal hs
      (hstabO h hh he _ (Submodule.sub_starProjection_mem_orthogonal v))
  have hcap : ∀ v, S.starProjection (capRep k r π Fr₀ w₀ v) = capRep k r π Fr₀ w₀ (S.starProjection v) := by
    intro v
    have key := P.Qx8.capRep_intertwine (frame_swap hFr₀) hrep.1 hrep.2 WeylGroupFacts.uh_one
      (S.starProjection : Wp →L[ℂ] Wp) (fun h' hh' he' v => by
        rw [inv_one, Matrix.one_mul, Matrix.mul_one]; exact hcomm h' hh' he' v) w₀ v
    simpa only [Matrix.one_mulVec] using key
  have hAx : S.starProjection x = 0 := by
    have h1 := hmem _ (S.starProjection_apply_mem x) Fr₀ hFr₀ w₀
    rw [← hcap, hx Fr₀ hFr₀ w₀, map_smul] at h1
    have h2 : (f w₀ - g w₀) • S.starProjection x = 0 := by rw [sub_smul, h1, sub_self]
    exact (smul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 hw₀)
  have hyS : y ∈ S := Submodule.subset_span hy
  rw [← (Submodule.starProjection_eq_self_iff).2 hyS, ← Submodule.inner_starProjection_left_eq_right, hAx, inner_zero_left]

end Formalism.FourierDecayAlt.P.CutMP.JA.PRhoCut
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASSnRepThConst
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField
open scoped ComplexConjugate Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC

noncomputable section

def PolyRadial : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    2 ≤ P.k → ∀ (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    ActHyp P Bs X d → ∀ l ∈ Finset.Icc 1 (P.k - 1), ∀ S, IsSSPt P Bs d l S →
    ∀ Pr, PRho.PRhoSpec P Bs.z Bs.π Pr →
    ∀ Bw Bw' : Fin P.k → Fin (2 * P.r + P.k + 1) → ℂ, Q.IsFrameOf P.k P.r [Bs.z] Bw → Q.IsFrameOf P.k P.r [Bs.z'] Bw' →
    ∀ π ρ : M.Ty P, M.Up P l π ρ → ∃ (n : ℕ) (q : Polynomial ℂ), ∀ ζ ∈ Gauge.GC.Ann P,
      ∀ Xf ∈ NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' ζ,
        (Pr π (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ)).comp Xf = Xf →
        (((Complex.normSq ζ - P.TT : ℝ) : ℂ) ^ n) • (Pr ρ (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ)).comp (S ζ Xf) =
          q.eval ((Complex.normSq ζ : ℝ) : ℂ) • (Pr ρ (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ)).comp
            (tht P.k P.r Bs.z Bs.z' Bs.π Bs.π' Bw Bw' (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ)
              (SSn.nu0' P.k P.r Bs.z Bs.z' Bs.μsec ζ) (SSn.io0 P.k P.r Bs.z Bs.z' Bs.μsec ζ) Xf)

def ModConst : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    2 ≤ P.k → ∀ (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    ActHyp P Bs X d → ∀ l ∈ Finset.Icc 1 (P.k - 1), ∀ S, IsSSPt P Bs d l S →
    ∀ Pr, PRho.PRhoSpec P Bs.z Bs.π Pr →
    ∀ Bw Bw' : Fin P.k → Fin (2 * P.r + P.k + 1) → ℂ, Q.IsFrameOf P.k P.r [Bs.z] Bw → Q.IsFrameOf P.k P.r [Bs.z'] Bw' →
    ∀ π ρ : M.Ty P, M.Up P l π ρ → ∃ c₁ c₂ : ℝ, ∀ ζ ∈ Gauge.GC.Ann P,
      ∀ Xf ∈ NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' ζ,
        (Pr π (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ)).comp Xf = Xf →
        ‖B.hsVec ((Pr ρ (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ)).comp (S ζ Xf))‖ ^ 2 = c₁ * ‖B.hsVec Xf‖ ^ 2 ∧
        ‖B.hsVec ((Pr ρ (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ)).comp
            (tht P.k P.r Bs.z Bs.z' Bs.π Bs.π' Bw Bw' (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ)
              (SSn.nu0' P.k P.r Bs.z Bs.z' Bs.μsec ζ) (SSn.io0 P.k P.r Bs.z Bs.z' Bs.μsec ζ) Xf))‖ ^ 2 =
          c₂ * ‖B.hsVec Xf‖ ^ 2

def LineNonzero : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π' → 2 ≤ P.k → ∀ Pr, PRho.PRhoSpec P Bs.z Bs.π Pr →
    ∀ (π : M.Ty P), ∀ ζ ∈ Gauge.GC.Ann P, ∃ Xf ∈ NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' ζ,
      (Pr π (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ)).comp Xf = Xf ∧ Xf ≠ 0

def PolyFinish : Prop :=
  ∀ (q : Polynomial ℂ) (n : ℕ) (a C : ℝ),
    (∀ x : ℝ, a < x → Complex.normSq (q.eval (x : ℂ)) = C * (x - a) ^ (2 * n)) →
    ∃ c : ℂ, q = Polynomial.C c * (Polynomial.X - Polynomial.C (a : ℂ)) ^ n

def ThConstOfCut : Prop := PolyRadial → ModConst → LineNonzero → PolyFinish → ThConst

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC
end

