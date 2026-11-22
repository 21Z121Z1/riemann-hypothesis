import Mathlib
import CompanionTheory.AutomorphicTheory.ZuckermanCommutation.ZuckermanFunctors.IsSimpleFam
import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.SmoothCyclicVectors.SmoothCyc
import CompanionTheory.AutomorphicTheory.BesselOrbitBounds.BesselMapUniqueness.BesselMapUniqGap
import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.SmoothCyclicVectors.PhMeas
import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.IwaCore

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.SnTens2
section
open CompanionTheory.Zuck BranchingSupport Matrix Finset
open scoped InnerProductSpace Kronecker

noncomputable section

namespace GlobalTheory.CompanionTheory.ZuckTensHom

variable {k r : ℕ}

theorem sum_list_comm {α β : Type} [Fintype β] (l : List α) (a : α → β → ℝ) :
    ∑ e, (l.map fun w => a w e).sum = (l.map fun w => ∑ e, a w e).sum := by
  induction l with
  | nil => simp
  | cons w l ih => simp [Finset.sum_add_distrib, ih]

theorem act_apply (X : Obj k r) (g : Formalism.FourierDecayAlt.ThreeDimData.Mx k r) (x : M X) (c : X.1.ι) :
    CompanionTheory.Zuck.act X g x c = ∑ d, X.1.ρ g c d • X.2.sig g (x d) := by
  simp only [CompanionTheory.Zuck.act, CompanionTheory.Zuck.mAct, CompanionTheory.Zuck.dOp, LinearMap.comp_apply, LinearMap.pi_apply,
    LinearMap.sum_apply, Finset.sum_apply, LinearMap.smul_apply, LinearMap.proj_apply,
    LinearMap.compLeft_apply, Function.comp_apply]

theorem act_tens1 (F E : FRep k r) (U : URep k r) (g : Formalism.FourierDecayAlt.ThreeDimData.Mx k r) (x : M (F.tens E, U)) (e : E.ι) :
    (fun c => CompanionTheory.Zuck.act (F.tens E, U) g x (c, e) : M (F, U)) =
      ∑ e', E.ρ g e e' • CompanionTheory.Zuck.act (F, U) g (fun c' => x (c', e')) := by
  funext c
  rw [act_apply]
  simp only [Finset.sum_apply, Pi.smul_apply, act_apply, Finset.smul_sum, smul_smul]
  show ∑ d : F.ι × E.ι, _ = _
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl fun e' _ => Finset.sum_congr rfl fun c' _ => ?_
  simp [CompanionTheory.Zuck.FRep.tens, mul_comm]

theorem act_tens2 (F E : FRep k r) (U : URep k r) (g : Formalism.FourierDecayAlt.ThreeDimData.Mx k r) (x : M (E.tens F, U)) (e : E.ι) :
    (fun c => CompanionTheory.Zuck.act (E.tens F, U) g x (e, c) : M (F, U)) =
      ∑ e', E.ρ g e e' • CompanionTheory.Zuck.act (F, U) g (fun c' => x (e', c')) := by
  funext c
  rw [act_apply]
  simp only [Finset.sum_apply, Pi.smul_apply, act_apply, Finset.smul_sum, smul_smul]
  show ∑ d : E.ι × F.ι, _ = _
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun e' _ => Finset.sum_congr rfl fun c' _ => ?_
  simp [CompanionTheory.Zuck.FRep.tens]

theorem sn_tens1 (F E : FRep k r) (U : URep k r) (W : List (Formalism.FourierDecayAlt.ThreeDimData.Mx k r)) (x : M (F.tens E, U)) :
    sn (F.tens E, U) W x = ∑ e, sn (F, U) W (fun c => x (c, e)) := by
  simp only [CompanionTheory.Zuck.sn]
  show ∑ d : F.ι × E.ι, _ = _
  rw [Fintype.sum_prod_type, Finset.sum_comm]

theorem sn_tens2 (F E : FRep k r) (U : URep k r) (W : List (Formalism.FourierDecayAlt.ThreeDimData.Mx k r)) (x : M (E.tens F, U)) :
    sn (E.tens F, U) W x = ∑ e, sn (F, U) W (fun c => x (e, c)) := by
  simp only [CompanionTheory.Zuck.sn]
  show ∑ d : E.ι × F.ι, _ = _
  rw [Fintype.sum_prod_type]

theorem tensHom : TensHom := by
  intro k r F F' E U U' f hf
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · intro W hW
    obtain ⟨C, Ws, hWs, hb⟩ := hf.cont W hW
    refine ⟨C, Ws, hWs, fun x => ?_⟩
    rw [sn_tens1]
    calc ∑ e, CompanionTheory.Zuck.sn (F', U') W (fun c => CompanionTheory.Zuck.on1 f x (c, e))
        = ∑ e, CompanionTheory.Zuck.sn (F', U') W (f (fun c => x (c, e))) := rfl
      _ ≤ ∑ e, C * (Ws.map fun W' => CompanionTheory.Zuck.sn (F, U) W' (fun c => x (c, e))).sum :=
          Finset.sum_le_sum fun e _ => hb _
      _ = C * ∑ e, (Ws.map fun W' => CompanionTheory.Zuck.sn (F, U) W' (fun c => x (c, e))).sum := by
          rw [Finset.mul_sum]
      _ = C * (Ws.map fun W' => ∑ e, CompanionTheory.Zuck.sn (F, U) W' (fun c => x (c, e))).sum :=
          congrArg (C * ·) (sum_list_comm Ws (fun W' e => CompanionTheory.Zuck.sn (F, U) W' (fun c => x (c, e))))
      _ = C * (Ws.map fun W' => CompanionTheory.Zuck.sn (F.tens E, U) W' x).sum := by
          simp only [sn_tens1]
  · intro g hg
    apply LinearMap.ext
    intro x
    funext p
    obtain ⟨c', e⟩ := p
    have h2 := act_tens1 F E U g x e
    have h1 := act_tens1 F' E U' g (CompanionTheory.Zuck.on1 f x) e
    calc (CompanionTheory.Zuck.on1 f ∘ₗ CompanionTheory.Zuck.act (F.tens E, U) g) x (c', e)
        = f (fun c => CompanionTheory.Zuck.act (F.tens E, U) g x (c, e)) c' := rfl
      _ = f (∑ e', E.ρ g e e' • CompanionTheory.Zuck.act (F, U) g (fun c => x (c, e'))) c' :=
          congrArg (fun y => f y c') h2
      _ = ∑ e', E.ρ g e e' • CompanionTheory.Zuck.act (F', U') g (f (fun c => x (c, e'))) c' := by
          rw [map_sum]
          simp only [map_smul, Finset.sum_apply, Pi.smul_apply]
          refine Finset.sum_congr rfl fun e' _ => ?_
          have hq := LinearMap.congr_fun (hf.equiv g hg) (fun c => x (c, e'))
          simp only [LinearMap.comp_apply] at hq
          rw [hq]
      _ = (∑ e', E.ρ g e e' • CompanionTheory.Zuck.act (F', U') g (fun c => CompanionTheory.Zuck.on1 f x (c, e'))) c' := by
          simp only [Finset.sum_apply, Pi.smul_apply]
          rfl
      _ = (fun c => CompanionTheory.Zuck.act (F'.tens E, U') g (CompanionTheory.Zuck.on1 f x) (c, e)) c' :=
          (congrFun h1 c').symm
      _ = (CompanionTheory.Zuck.act (F'.tens E, U') g ∘ₗ CompanionTheory.Zuck.on1 f) x (c', e) := rfl
  · intro W hW
    obtain ⟨C, Ws, hWs, hb⟩ := hf.cont W hW
    refine ⟨C, Ws, hWs, fun x => ?_⟩
    rw [sn_tens2]
    calc ∑ e, CompanionTheory.Zuck.sn (F', U') W (fun c => CompanionTheory.Zuck.on2 f x (e, c))
        = ∑ e, CompanionTheory.Zuck.sn (F', U') W (f (fun c => x (e, c))) := rfl
      _ ≤ ∑ e, C * (Ws.map fun W' => CompanionTheory.Zuck.sn (F, U) W' (fun c => x (e, c))).sum :=
          Finset.sum_le_sum fun e _ => hb _
      _ = C * ∑ e, (Ws.map fun W' => CompanionTheory.Zuck.sn (F, U) W' (fun c => x (e, c))).sum := by
          rw [Finset.mul_sum]
      _ = C * (Ws.map fun W' => ∑ e, CompanionTheory.Zuck.sn (F, U) W' (fun c => x (e, c))).sum :=
          congrArg (C * ·) (sum_list_comm Ws (fun W' e => CompanionTheory.Zuck.sn (F, U) W' (fun c => x (e, c))))
      _ = C * (Ws.map fun W' => CompanionTheory.Zuck.sn (E.tens F, U) W' x).sum := by
          simp only [sn_tens2]
  · intro g hg
    apply LinearMap.ext
    intro x
    funext p
    obtain ⟨e, c'⟩ := p
    have h2 := act_tens2 F E U g x e
    have h1 := act_tens2 F' E U' g (CompanionTheory.Zuck.on2 f x) e
    calc (CompanionTheory.Zuck.on2 f ∘ₗ CompanionTheory.Zuck.act (E.tens F, U) g) x (e, c')
        = f (fun c => CompanionTheory.Zuck.act (E.tens F, U) g x (e, c)) c' := rfl
      _ = f (∑ e', E.ρ g e e' • CompanionTheory.Zuck.act (F, U) g (fun c => x (e', c))) c' :=
          congrArg (fun y => f y c') h2
      _ = ∑ e', E.ρ g e e' • CompanionTheory.Zuck.act (F', U') g (f (fun c => x (e', c))) c' := by
          rw [map_sum]
          simp only [map_smul, Finset.sum_apply, Pi.smul_apply]
          refine Finset.sum_congr rfl fun e' _ => ?_
          have hq := LinearMap.congr_fun (hf.equiv g hg) (fun c => x (e', c))
          simp only [LinearMap.comp_apply] at hq
          rw [hq]
      _ = (∑ e', E.ρ g e e' • CompanionTheory.Zuck.act (F', U') g (fun c => CompanionTheory.Zuck.on2 f x (e', c))) c' := by
          simp only [Finset.sum_apply, Pi.smul_apply]
          rfl
      _ = (fun c => CompanionTheory.Zuck.act (E.tens F', U') g (CompanionTheory.Zuck.on2 f x) (e, c)) c' :=
          (congrFun h1 c').symm
      _ = (CompanionTheory.Zuck.act (E.tens F', U') g ∘ₗ CompanionTheory.Zuck.on2 f) x (e, c') := rfl

end GlobalTheory.CompanionTheory.ZuckTensHom

end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ToRawComplex
section
open CompanionTheory.Zuck BranchingSupport Matrix Finset
open scoped InnerProductSpace Kronecker

noncomputable section

namespace GlobalTheory.CompanionTheory.ZuckToRaw

variable {k r : ℕ}

theorem dsigW_zero' (R : Rep k r) (W : List (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)) :
    PI.UpqRep.dsigW (k := k) (r := r) R.σ W (0 : R.H) = 0 := by
  induction W with
  | nil => rfl
  | cons X W ih =>
    show PI.UpqRep.dsig (k := k) (r := r) R.σ X (PI.UpqRep.dsigW (k := k) (r := r) R.σ W 0) = 0
    rw [ih]
    simp [PI.UpqRep.dsig]

open Classical in

def extZ {R R' : Rep k r} (f : R.smSub →ₗ[ℂ] R'.smSub) (y : R.H) : R'.H :=
  if h : y ∈ R.smSub then (f ⟨y, h⟩ : R'.H) else 0

theorem extZ_coe {R R' : Rep k r} (f : R.smSub →ₗ[ℂ] R'.smSub) (y : R.smSub) :
    extZ f (y : R.H) = (f y : R'.H) := by
  simp only [extZ, dif_pos y.2]

theorem smMap_extZ {R R' : Rep k r} (f : R.smSub →ₗ[ℂ] R'.smSub)
    (hf : ∀ W, LieWd k r W → ∃ (C : ℝ) (Ws : List (List (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ))), (∀ W' ∈ Ws, LieWd k r W') ∧
      ∀ y : R.smSub, ‖PI.UpqRep.dsigW (k := k) (r := r) R'.σ W (f y : R'.H)‖ ≤
        C * (Ws.map fun W' => ‖PI.UpqRep.dsigW (k := k) (r := r) R.σ W' (y : R.H)‖).sum) :
    SmMap R R' (extZ f) where
  mem v hv := by
    have := extZ_coe f ⟨v, hv⟩
    rw [show extZ f v = _ from this]
    exact (f _).2
  add v hv w hw := by
    have h1 := extZ_coe f ⟨v, hv⟩
    have h2 := extZ_coe f ⟨w, hw⟩
    have h3 := extZ_coe f (⟨v, hv⟩ + ⟨w, hw⟩)
    rw [show extZ f v = _ from h1, show extZ f w = _ from h2, show extZ f (v + w) = _ from h3, map_add]
    rfl
  smul a v hv := by
    have h1 := extZ_coe f ⟨v, hv⟩
    have h3 := extZ_coe f (a • ⟨v, hv⟩)
    rw [show extZ f v = _ from h1, show extZ f (a • v) = _ from h3, map_smul]
    rfl
  cont W hW := by
    obtain ⟨C, Ws, h1, h2⟩ := hf W hW
    refine ⟨C, Ws, h1, fun v hv => ?_⟩
    have h3 := extZ_coe f ⟨v, hv⟩
    show ‖PI.UpqRep.dsigW (k := k) (r := r) R'.σ W (extZ f v)‖ ≤ _
    rw [show extZ f v = _ from h3]
    exact h2 ⟨v, hv⟩

theorem sn_single (X : Obj k r) (W : List (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)) (c : X.1.ι) (v : X.2.R.smSub) :
    sn X W (Pi.single c v) = ‖PI.UpqRep.dsigW (k := k) (r := r) X.2.R.σ W (v : X.2.R.H)‖ := by
  unfold sn
  rw [Finset.sum_eq_single c]
  · simp
  · intro b _ hb
    rw [Pi.single_eq_of_ne hb, ZeroMemClass.coe_zero, dsigW_zero', norm_zero]
  · simp

theorem le_sn (X : Obj k r) (W : List (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)) (c : X.1.ι) (x : M X) :
    ‖PI.UpqRep.dsigW (k := k) (r := r) X.2.R.σ W (x c : X.2.R.H)‖ ≤ sn X W x :=
  Finset.single_le_sum (f := fun c => ‖PI.UpqRep.dsigW (k := k) (r := r) X.2.R.σ W (x c : X.2.R.H)‖)
    (fun _ _ => norm_nonneg _) (Finset.mem_univ c)

def coord {X Y : Obj k r} (f : M X →ₗ[ℂ] M Y) (d : Y.1.ι) (c : X.1.ι) : X.2.R.smSub →ₗ[ℂ] Y.2.R.smSub :=
  LinearMap.proj d ∘ₗ f ∘ₗ LinearMap.single ℂ (fun _ : X.1.ι => X.2.R.smSub) c

theorem coord_apply {X Y : Obj k r} (f : M X →ₗ[ℂ] M Y) (d : Y.1.ι) (c : X.1.ι) (v : X.2.R.smSub) :
    coord f d c v = f (Pi.single c v) d := rfl

theorem smMap_coord {X Y : Obj k r} {f : M X →ₗ[ℂ] M Y} (hf : IsHom X Y f) (d : Y.1.ι) (c : X.1.ι) :
    SmMap X.2.R Y.2.R (extZ (coord f d c)) := by
  refine smMap_extZ _ fun W hW => ?_
  obtain ⟨C, Ws, h1, h2⟩ := hf.cont W hW
  refine ⟨C, Ws, h1, fun y => ?_⟩
  have := (le_sn Y W d _).trans (h2 (Pi.single c y))
  simpa only [sn_single, coord_apply] using this

theorem sum_coord {X Y : Obj k r} (f : M X →ₗ[ℂ] M Y) (d : Y.1.ι) (x : M X) :
    ∑ c, extZ (coord f d c) (x c : X.2.R.H) = (f x d : Y.2.R.H) := by
  simp only [extZ_coe, coord_apply]
  conv_rhs => rw [← Finset.univ_sum_single x, map_sum, Finset.sum_apply]
  simp

theorem act_coe (X : Obj k r) {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hg : g ∈ GG k r) (x : M X) (c : X.1.ι) :
    (CompanionTheory.Zuck.act X g x c : X.2.R.H) = BranchingSupport.act X.1.ρ X.2.R g (fun d => (x d : X.2.R.H)) c := by
  simp [CompanionTheory.Zuck.act, BranchingSupport.act, mAct, dOp, URep.sig_coe _ hg]

theorem one_coord {U : URep k r} {Y : Obj k r} (f : M (one U) →ₗ[ℂ] M Y) (d : Y.1.ι) (x : M (one U)) :
    extZ (coord f d ()) (x () : U.R.H) = (f x d : Y.2.R.H) := by
  rw [← sum_coord f d x]
  simp

theorem act_one (U : URep k r) {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hg : g ∈ GG k r) (x : M (one U)) :
    (CompanionTheory.Zuck.act (one U) g x () : U.R.H) = U.R.σ g (x ()) := by
  rw [act_coe (one U) hg]
  simp [BranchingSupport.act]

theorem toRaw : ToRaw := by
  rintro k r F U κ _ _ T ⟨io, pr, h⟩
  refine ⟨fun a c => extZ (coord (io a) c ()), fun a c => extZ (coord (pr a) () c), ?_⟩
  refine ⟨fun I c => smMap_coord (h.io_hom I) c (), fun I c => smMap_coord (h.pr_hom I) () c,
    fun I g hg y hy => ?_, fun I g hg x hx => ?_, fun x hx c => ?_, fun I y hy => ?_, fun I J hIJ y hy => ?_⟩
  · let y' : M (one (T I)) := fun _ => ⟨y, hy⟩
    funext c
    have e1 : (T I).R.σ g y = (CompanionTheory.Zuck.act (one (T I)) g y' () : (T I).R.H) := (act_one (T I) hg y').symm
    have e2 : ∀ d, extZ (coord (io I) d ()) y = (io I y' d : U.R.H) := fun d => one_coord (io I) d y'
    have e3 := LinearMap.congr_fun ((h.io_hom I).equiv g hg) y'
    simp only [LinearMap.comp_apply] at e3
    simp only [e2]
    rw [e1, one_coord, e3]
    exact act_coe (F, U) hg _ c
  · let x' : M (F, U) := fun c => ⟨x c, hx c⟩
    have e1 : ∀ c, BranchingSupport.act F.ρ U.R g x c = (CompanionTheory.Zuck.act (F, U) g x' c : U.R.H) :=
      fun c => (act_coe (F, U) hg x' c).symm
    have e2 : ∑ c, extZ (coord (pr I) () c) (x c) = (pr I x' () : (T I).R.H) := sum_coord (pr I) () x'
    have e3 := LinearMap.congr_fun ((h.pr_hom I).equiv g hg) x'
    simp only [LinearMap.comp_apply] at e3
    simp only [e1]
    rw [e2, ← act_one (T I) hg, ← e3]
    exact sum_coord (pr I) () _
  · let x' : M (F, U) := fun c => ⟨x c, hx c⟩
    have e2 : ∀ I, ∑ c, extZ (coord (pr I) () c) (x c) = (pr I x' () : (T I).R.H) :=
      fun I => sum_coord (pr I) () x'
    have e4 : ∀ I, extZ (coord (io I) c ()) (pr I x' () : (T I).R.H) = (io I (pr I x') c : U.R.H) :=
      fun I => one_coord (io I) c _
    have e3 := congrFun (LinearMap.congr_fun h.sum x') c
    simp only [LinearMap.coe_sum, Finset.sum_apply, LinearMap.comp_apply, LinearMap.id_apply] at e3
    simp only [e2, e4]
    rw [← Submodule.coe_sum, e3]
  · let y' : M (one (T I)) := fun _ => ⟨y, hy⟩
    have e2 : ∀ d, extZ (coord (io I) d ()) y = (io I y' d : U.R.H) := fun d => one_coord (io I) d y'
    have e3 := LinearMap.congr_fun (h.pr_io I) y'
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at e3
    simp only [e2]
    refine (sum_coord (pr I) () (io I y')).trans ?_
    rw [e3]
  · let y' : M (one (T J)) := fun _ => ⟨y, hy⟩
    have e2 : ∀ d, extZ (coord (io J) d ()) y = (io J y' d : U.R.H) := fun d => one_coord (io J) d y'
    have e3 := LinearMap.congr_fun (h.pr_io_ne I J hIJ) y'
    simp only [LinearMap.comp_apply, LinearMap.zero_apply] at e3
    simp only [e2]
    refine (sum_coord (pr I) () (io J y')).trans ?_
    rw [e3]
    rfl

end GlobalTheory.CompanionTheory.ZuckToRaw

end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.TorBound
section
open Matrix CompanionTheory.Bmu Formalism.QuantumDeterminants CompanionTheory.D.Upq.Sm

noncomputable section

namespace GlobalTheory.CompanionTheory.BmuTorBound

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem step_le (k r : ℕ) (d : Fin (2 * r + k + 1) → ℝ) (M : ℝ) (hd : IsTor k r d) (hM : 1 ≤ M)
    (ha : ∀ a : Fin r, d (eI k r a) ≤ M * d (nxt k r a)) (j : ℕ) (hj : j + 1 < 2 * r + k + 1) :
    d ⟨j, by omega⟩ ≤ M * d ⟨j + 1, hj⟩ := by
  obtain ⟨hpos, hpair, hmid, hf⟩ := hd
  by_cases h1 : j < r
  · exact ha ⟨j, h1⟩
  by_cases h2 : r + k ≤ j
  · have hlt : 2 * r + k - j - 1 < r := by omega
    have h := ha ⟨2 * r + k - j - 1, hlt⟩
    have p1 := hpair ⟨j, by omega⟩ (nxt k r ⟨2 * r + k - j - 1, hlt⟩) (Or.inr h2) (by simp only [nxt]; omega)
    have p2 := hpair ⟨j + 1, hj⟩ (eI k r ⟨2 * r + k - j - 1, hlt⟩) (Or.inr (by simp only; omega))
      (by simp only [eI]; omega)
    have q1 := hpos ⟨j, by omega⟩
    have q2 := hpos ⟨j + 1, hj⟩
    generalize d ⟨j, by omega⟩ = x at *
    generalize d ⟨j + 1, hj⟩ = y at *
    generalize d (nxt k r ⟨2 * r + k - j - 1, hlt⟩) = u at *
    generalize d (eI k r ⟨2 * r + k - j - 1, hlt⟩) = v at *
    calc x = x * y * v := by rw [mul_assoc, p2, mul_one]
      _ ≤ x * y * (M * u) := mul_le_mul_of_nonneg_left h (by positivity)
      _ = M * y * (x * u) := by ring
      _ = M * y := by rw [p1, mul_one]
  have a1 : d ⟨j, by omega⟩ ≤ 1 := by
    by_cases h3 : j = r
    · have : (⟨j, by omega⟩ : Fin (2 * r + k + 1)) = wI k r 0 := Fin.ext (by simp [wI, h3])
      rw [this]; exact hf
    · exact (hmid _ (by simp only [outer]; omega)).le
  have a2 : 1 ≤ d ⟨j + 1, hj⟩ := by
    by_cases h3 : j + 1 = r + k
    · have p := hpair ⟨j + 1, hj⟩ (wI k r 0) (Or.inr (by simp only; omega)) (by simp [wI]; omega)
      have q := hpos ⟨j + 1, hj⟩
      nlinarith
    · exact (hmid _ (by simp only [outer]; omega)).ge
  nlinarith

theorem chain_le {n : ℕ} (d : Fin n → ℝ) (M : ℝ) (hM : 1 ≤ M)
    (hs : ∀ (j : ℕ) (hj : j + 1 < n), d ⟨j, by omega⟩ ≤ M * d ⟨j + 1, hj⟩) (j m : ℕ) (h : j + m < n) :
    d ⟨j, by omega⟩ ≤ M ^ m * d ⟨j + m, h⟩ := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h1 := ih (by omega)
    have h2 := hs (j + m) h
    calc d ⟨j, by omega⟩ ≤ M ^ m * d ⟨j + m, by omega⟩ := h1
      _ ≤ M ^ m * (M * d ⟨j + m + 1, h⟩) := mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = M ^ (m + 1) * d ⟨j + (m + 1), h⟩ := by rw [pow_succ, mul_assoc]; rfl

theorem ratio_le (k r : ℕ) (d : Fin (2 * r + k + 1) → ℝ) (M : ℝ) (hd : IsTor k r d) (hM : 1 ≤ M)
    (ha : ∀ a : Fin r, d (eI k r a) ≤ M * d (nxt k r a)) (i j : Fin (2 * r + k + 1)) (h : ¬ up k r i j) :
    d j ≤ M ^ (2 * r + k + 1) * d i := by
  by_cases hij : i < j
  · have hi : ¬ outer k r i := fun h' => h ⟨hij, Or.inl h'⟩
    have hj : ¬ outer k r j := fun h' => h ⟨hij, Or.inr h'⟩
    rw [hd.2.2.1 i hi, hd.2.2.1 j hj, mul_one]
    exact one_le_pow₀ hM
  · have hji : j.val ≤ i.val := by
      have := not_lt.mp hij
      exact this
    have hc := chain_le d M hM (step_le k r d M hd hM ha) j.val (i.val - j.val) (by have := i.2; omega)
    have e : (⟨j.val + (i.val - j.val), by have := i.2; omega⟩ : Fin (2 * r + k + 1)) = i :=
      Fin.ext (by simp only; omega)
    rw [e] at hc
    refine hc.trans (mul_le_mul_of_nonneg_right ?_ (hd.1 i).le)
    exact pow_le_pow_right₀ hM (by have := i.2; omega)

theorem unitary_conj_le {n : ℕ} (R B : Mat n) (hR : Rᴴ * R = 1) : ‖Rᴴ * B * R‖ ≤ (n : ℝ) ^ 2 * ‖B‖ := by
  have hU : R ∈ Matrix.unitaryGroup (Fin n) ℂ := Matrix.mem_unitaryGroup_iff'.mpr hR
  have he : ∀ i j, ‖R i j‖ ≤ 1 := fun i j => entry_norm_bound_of_unitary hU i j
  rw [Matrix.norm_le_iff (by positivity)]
  intro i j
  have h1 : ∀ l, ‖(Rᴴ * B) i l‖ ≤ n * ‖B‖ := by
    intro l
    rw [Matrix.mul_apply]
    refine (norm_sum_le _ _).trans ?_
    refine (Finset.sum_le_card_nsmul _ _ ‖B‖ ?_).trans (by simp)
    intro x _
    rw [norm_mul, Matrix.conjTranspose_apply, norm_star]
    calc ‖R x i‖ * ‖B x l‖ ≤ 1 * ‖B‖ :=
          mul_le_mul (he x i) (Matrix.norm_entry_le_entrywise_sup_norm B) (norm_nonneg _) zero_le_one
      _ = ‖B‖ := one_mul _
  rw [Matrix.mul_apply]
  refine (norm_sum_le _ _).trans ?_
  refine (Finset.sum_le_card_nsmul _ _ (n * ‖B‖) ?_).trans (by simp [sq, mul_assoc])
  intro x _
  rw [norm_mul]
  calc ‖(Rᴴ * B) i x‖ * ‖R x j‖ ≤ n * ‖B‖ * 1 :=
        mul_le_mul (h1 x) (he x j) (norm_nonneg _) (by positivity)
    _ = n * ‖B‖ := mul_one _

theorem torBound : TorBound := by
  intro k r d R A M _ hd hR hM ha hA
  have hpos := hd.1
  have hinv : (dg d * R)⁻¹ = Rᴴ * dg (fun i => (d i)⁻¹) := by
    apply Matrix.inv_eq_left_inv
    have : dg (fun i => (d i)⁻¹) * dg d = 1 := by
      unfold dg
      rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1
      funext i
      rw [← Complex.ofReal_mul, inv_mul_cancel₀ (hpos i).ne', Complex.ofReal_one]
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (dg _), this, Matrix.one_mul, hR]
  have e : (dg d * R)⁻¹ * A * (dg d * R) = Rᴴ * (dg (fun i => (d i)⁻¹) * A * dg d) * R := by
    rw [hinv]; simp only [Matrix.mul_assoc]
  rw [e]
  refine (unitary_conj_le R _ hR).trans ?_
  rw [mul_assoc _ ‖A‖]
  refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
  rw [Matrix.norm_le_iff (by positivity)]
  intro i j
  unfold dg
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases hu : up k r i j
  · rw [hA i j hu]
    simp only [mul_zero, zero_mul, norm_zero]
    positivity
  · have hr := ratio_le k r d M hd hM ha i j hu
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg (hpos j).le,
      Real.norm_of_nonneg (inv_pos.mpr (hpos i)).le]
    have h2 : (d i)⁻¹ * d j ≤ M ^ (2 * r + k + 1) := by
      rw [inv_mul_le_iff₀ (hpos i), mul_comm]; exact hr
    have hi := hpos i
    have hj := hpos j
    calc (d i)⁻¹ * ‖A i j‖ * d j = ‖A i j‖ * ((d i)⁻¹ * d j) := by ring
      _ ≤ ‖A‖ * M ^ (2 * r + k + 1) :=
        mul_le_mul (Matrix.norm_entry_le_entrywise_sup_norm A) h2 (by positivity) (norm_nonneg _)

end GlobalTheory.CompanionTheory.BmuTorBound
end
end

