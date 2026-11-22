import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0007
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0074

-- bundled from Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChartNonempty
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix
open scoped TensorProduct Classical

namespace GlobalTheory.AdForm.Model
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7}

section Gen
variable (θ : InfFam D) (V : HSp D) {n : ℕ} (hn : V.rank = n)

theorem mt_mul (g h : GA D V) : mt V (g * h) = mt V g * mt V h := by
  simp only [Formalism.L2.Theta.mt, map_mul, Units.val_mul]

theorem mt_one : mt V (1 : GA D V) = 1 := by
  simp only [Formalism.L2.Theta.mt, map_one, Units.val_one]

theorem finM_mul (g h : GA D V) : finM V hn (g * h) = finM V hn g * finM V hn h := by
  subst hn
  simp only [finM, mt_mul, finCongr_refl, Matrix.reindex_refl_refl]
  exact Matrix.map_mul

theorem finM_one : finM V hn (1 : GA D V) = 1 := by
  subst hn
  simp only [finM, mt_one, finCongr_refl, Matrix.reindex_refl_refl]
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem infM_eq (g : GA D V) (τ : D.what₂.Tau) :
    infM θ V hn g τ = ((mt V g).map ((θ τ).comp (infPart D))).reindex (finCongr hn) (finCongr hn) := rfl

theorem infM_mul (g h : GA D V) (τ : D.what₂.Tau) : infM θ V hn (g * h) τ = infM θ V hn g τ * infM θ V hn h τ := by
  subst hn
  simp only [infM_eq, mt_mul, finCongr_refl, Matrix.reindex_refl_refl]
  exact Matrix.map_mul

theorem infM_one (τ : D.what₂.Tau) : infM θ V hn (1 : GA D V) τ = 1 := by
  subst hn
  simp only [infM_eq, mt_one, finCongr_refl, Matrix.reindex_refl_refl]
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem infM_unit (g : GA D V) (τ : D.what₂.Tau) : IsUnit (infM θ V hn g τ).det := by
  have h := infM_mul θ V hn g g⁻¹ τ
  rw [mul_inv_cancel, infM_one] at h
  exact Matrix.isUnit_det_of_right_inverse h.symm

def finGL (g : GA D V) : GL (Fin n) (EF D) :=
  ⟨finM V hn g, finM V hn g⁻¹, by rw [← finM_mul, mul_inv_cancel, finM_one], by rw [← finM_mul, inv_mul_cancel, finM_one]⟩

theorem toEAf_conj (a : AE D) :
    toEAf D (cA D a) = Formalism.UG.sigR (sigD D) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (toEAf D a) := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => rfl
  | add x y hx hy => rw [RingHom.map_add, RingHom.map_add, RingHom.map_add, RingHom.map_add, hx, hy]

theorem toEAf_inc (e : D.host.E) : toEAf D (incA D e) = inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) e := rfl

theorem finGL_mem (g : GA D V) :
    finGL V hn g ∈ UPts (sigD D) (V.gram.reindex (finCongr hn) (finCongr hn)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) := by
  subst hn
  have hg : cT (cA D) (mt V g) * V.gram.map (incA D) * mt V g = V.gram.map (incA D) := g.2
  have h2 := congrArg (fun M => M.map (toEAf D)) hg
  simp only [Matrix.map_mul] at h2
  change cT _ (finM V rfl g) * _ * finM V rfl g = _
  simp only [finM, finCongr_refl, Matrix.reindex_refl_refl]
  have e1 : cT (Formalism.UG.sigR (sigD D) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) ((mt V g).map (toEAf D)) =
      (cT (cA D) (mt V g)).map (toEAf D) := by
    ext i j; simp only [cT, Matrix.transpose_apply, Matrix.map_apply, toEAf_conj]
  have e2 : V.gram.map (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) = (V.gram.map (incA D)).map (toEAf D) := rfl
  rw [e1, e2]; exact h2

def trFr {G : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ} (g : GA D V) (y : Frames G) : Frames G :=
  ⟨fun τ => infM θ V hn g τ * y.1 τ, fun τ => by rw [Matrix.det_mul]; exact (infM_unit θ V hn g τ).mul (y.2 τ)⟩

variable {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 D.host.F))}
  (S : StepLevel D.host.F D.host.E (sigD D) (V.gram.reindex (finCongr hn) (finCongr hn)) T f bad) {cl : Type}
  (yc : cl → UPts (sigD D) (V.gram.reindex (finCongr hn) (finCongr hn)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))

theorem exists_dec (hy : Function.Surjective (fun c => (Quotient.mk'' (yc c) : Cls S))) (g : GA D V) :
    ∃ p, IsDec S yc (finM V hn g) p := by
  obtain ⟨c, hc⟩ := hy (Quotient.mk'' ⟨finGL V hn g, finGL_mem V hn g⟩)
  obtain ⟨a, ha, b, hb, hab⟩ := (DoubleCoset.eq _ _ (yc c) _).1 hc
  obtain ⟨γ, hγ, e⟩ := Subgroup.mem_subgroupOf.1 ha
  refine ⟨(c, γ, ⟨b.1, Subgroup.mem_subgroupOf.1 hb⟩), hγ, ?_⟩
  have := congrArg (fun x => x.1.1) hab
  simp only at this
  rw [e]; exact this

set_option maxHeartbeats 2000000 in

theorem rdS_res (hy : Function.Surjective (fun c => (Quotient.mk'' (yc c) : Cls S)))
    (Ψ) (hΨ : Ψ ∈ AdFun S (embT D)) (y : Frames (gramC _ (embT D))) (g : GA D V) :
    rdS θ V hn S yc (fun c => Ψ (yc c)) y g = Ψ ⟨finGL V hn g, finGL_mem V hn g⟩ (trFr θ V hn g y) := by
  have h := exists_dec V hn S yc hy g
  rw [rdS, dif_pos h]
  obtain ⟨h1, h2⟩ := h.choose_spec
  generalize h.choose = p at h1 h2 ⊢
  have hi : ∀ τ, atInf (embT D) p.2.1.1 τ * atInf (embT D) (p.2.1⁻¹ : GL (Fin n) D.host.E).1 τ = 1 := by
    intro τ
    simp only [atInf]
    rw [← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]
  have hu : ∀ τ, IsUnit (atInf (embT D) (p.2.1⁻¹ : GL (Fin n) D.host.E).1 τ * infM θ V hn g τ * y.1 τ).det := by
    intro τ
    rw [Matrix.det_mul, Matrix.det_mul]
    exact ((Matrix.isUnit_det_of_left_inverse (hi τ)).mul (infM_unit θ V hn g τ)).mul (y.2 τ)
  rw [atFr, dif_pos hu]
  refine (hΨ p.2.1 h1 (yc p.1) _ p.2.2 (Units.ext h2) _ _ ?_).symm
  intro τ
  simp only [trFr]
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hi, Matrix.one_mul]

theorem rdS_left (hθ : IsInfFam θ) (hy : Function.Surjective (fun c => (Quotient.mk'' (yc c) : Cls S)))
    (Ψ) (hΨ : Ψ ∈ AdFun S (embT D)) (y : Frames (gramC _ (embT D))) (γ : GA D V) (hγ : γ ∈ GQ V) (g : GA D V) :
    rdS θ V hn S yc (fun c => Ψ (yc c)) y (γ * g) = rdS θ V hn S yc (fun c => Ψ (yc c)) y g := by
  rw [rdS_res θ V hn S yc hy Ψ hΨ, rdS_res θ V hn S yc hy Ψ hΨ]
  subst hn
  obtain ⟨δ, hδ, e⟩ := Subgroup.mem_subgroupOf.1 hγ
  have e' : mt V γ = δ.1.map (incA D) := congrArg Units.val e.symm
  have := hΨ δ hδ ⟨finGL V rfl g, finGL_mem V rfl g⟩ ⟨finGL V rfl (γ * g), finGL_mem V rfl (γ * g)⟩ 1 (by
      apply Units.ext
      change finM V rfl (γ * g) = _
      rw [finM_mul]
      simp only [OneMemClass.coe_one, mul_one, Units.val_mul]
      congr 1
      simp only [finM, e', finCongr_refl, Matrix.reindex_refl_refl]
      rfl)
    (trFr θ V rfl (γ * g) y) (trFr θ V rfl g y) (by
      intro τ
      simp only [trFr, infM_mul, Matrix.mul_assoc]
      congr 1
      simp only [infM_eq, e', finCongr_refl, Matrix.reindex_refl_refl]
      ext i j
      exact (hθ τ).1 _)
  simpa using this

theorem rdS_right_inf (ψ : cl → Frames (gramC (V.gram.reindex (finCongr hn) (finCongr hn)) (embT D)) → ℂ)
    (y : Frames (gramC _ (embT D))) (g k : GA D V) (hk : finM V hn k = 1) :
    rdS θ V hn S yc ψ y (g * k) = rdS θ V hn S yc ψ (trFr θ V hn k y) g := by
  have e : finM V hn (g * k) = finM V hn g := by rw [finM_mul, hk, mul_one]
  simp only [rdS, e, infM_mul, trFr, Matrix.mul_assoc]

set_option maxHeartbeats 2000000 in

theorem rdS_right_lev (hy : Function.Surjective (fun c => (Quotient.mk'' (yc c) : Cls S)))
    (Ψ) (hΨ : Ψ ∈ AdFun S (embT D)) (y : Frames (gramC _ (embT D))) (g k : GA D V) (κ : S.U)
    (hk : finM V hn k = κ.1.1) (hk' : ∀ τ, infM θ V hn k τ = 1) :
    rdS θ V hn S yc (fun c => Ψ (yc c)) y (g * k) = (S.chi κ : ℂ) * rdS θ V hn S yc (fun c => Ψ (yc c)) y g := by
  rw [rdS_res θ V hn S yc hy Ψ hΨ, rdS_res θ V hn S yc hy Ψ hΨ]
  refine hΨ 1 (one_mem _) _ _ κ ?_ _ _ ?_
  · apply Units.ext
    change finM V hn (g * k) = _
    rw [finM_mul, hk]
    simp only [map_one, one_mul, Units.val_mul]
    rfl
  · intro τ
    simp only [trFr, infM_mul, hk', atInf, Units.val_one, mul_one]
    rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul]

theorem rdS_at_rep (hy : Function.Surjective (fun c => (Quotient.mk'' (yc c) : Cls S)))
    (Ψ) (hΨ : Ψ ∈ AdFun S (embT D)) (y : Frames (gramC _ (embT D))) (g : GA D V) (c : cl)
    (hk : finM V hn g = (yc c).1.1) (hk' : ∀ τ, infM θ V hn g τ = 1) :
    rdS θ V hn S yc (fun c => Ψ (yc c)) y g = Ψ (yc c) y := by
  rw [rdS_res θ V hn S yc hy Ψ hΨ]
  congr 1
  · exact Subtype.ext (Units.ext hk)
  · apply Subtype.ext; funext τ; simp only [trFr, hk', Matrix.one_mul]

theorem rdS_add (ψ ψ' : cl → Frames (gramC (V.gram.reindex (finCongr hn) (finCongr hn)) (embT D)) → ℂ) (y) (g : GA D V) :
    rdS θ V hn S yc (ψ + ψ') y g = rdS θ V hn S yc ψ y g + rdS θ V hn S yc ψ' y g := by
  simp only [rdS, atFr]
  split_ifs
  · exact mul_add _ _ _
  · simp
  · simp

end Gen

variable {u : D.what₂.Word}

theorem chart_rd {i : ℕ} {hi : i ≤ D.R.m} (Q : Chart D u i hi) (θ : InfFam D)
    (ψ : (D.mem u).C.cls i → (D.mem u).C.Y i → ℂ) (Ψ) (hΨ : Ψ ∈ AdFun Q.K.lev (embT D))
    (hψ : ∀ c z, ψ (Q.inc c) (Q.eY.symm z) = Ψ (Q.K.y c) z) (y : (D.mem u).C.Y i) (g : GA D (D.sp.X i)) :
    Q.rd θ ψ y g = Ψ ⟨finGL _ (rankN D i hi) g, finGL_mem _ (rankN D i hi) g⟩ (trFr θ _ (rankN D i hi) g (Q.eY y)) := by
  have e : (fun c z => ψ (Q.inc c) (Q.eY.symm z)) = fun c => Ψ (Q.K.y c) := by funext c z; exact hψ c z
  rw [Chart.rd, e]
  exact rdS_res θ _ (rankN D i hi) Q.K.lev Q.K.y Q.K.y_bij.2 Ψ hΨ _ g

theorem chart_nonempty {i : ℕ} {hi : i ≤ D.R.m} (Q : Chart D u i hi) : Nonempty Q.cl :=
  ⟨(Q.K.y_bij.2 (Quotient.mk'' 1)).choose⟩

variable {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i} (F : FormsTiedSym D u Ch chOf)

theorem mid_left (i : ℕ) (h1 : 1 ≤ i) (h2 : i + 1 ≤ D.R.m) (β : Ch i) (θ : InfFam D) (hθ : IsInfFam θ)
    (ψ : (D.mem u).C.cls i → (D.mem u).C.Y i → ℂ) (hψ : ψ ∈ (D.fm u).Fi i) (y) (γ) (hγ : γ ∈ GQ (D.sp.X i)) (g) :
    rd F θ i (le_of_succ_m h2) β ψ y (γ * g) = rd F θ i (le_of_succ_m h2) β ψ y g := by
  have hc : chart F i (le_of_succ_m h2) β = midChart F i h1 h2 β := by
    rw [chart, dif_neg (by omega)]
  obtain ⟨Ψ, hΨ, e⟩ := ((F.valC i h1 h2).Fi ψ).1 hψ β
  rw [rd, hc, Chart.rd]
  have e' : (fun c z => ψ ((midChart F i h1 h2 β).inc c) ((midChart F i h1 h2 β).eY.symm z)) =
    fun c => Ψ ((midChart F i h1 h2 β).K.y c) := e.symm
  rw [e']
  exact rdS_left θ _ (rankN D i (le_of_succ_m h2)) _ _ hθ (midChart F i h1 h2 β).K.y_bij.2 Ψ hΨ.1 _ γ hγ g

theorem end_left (i : ℕ) (hi : i ≤ D.R.m) (h : i = 0 ∨ i = D.R.m) (β : Ch i) (θ : InfFam D) (hθ : IsInfFam θ)
    (ψ : (D.mem u).C.cls i → (D.mem u).C.Y i → ℂ) (hψ : ψ ∈ (D.fm u).Fi i) (y) (γ) (hγ : γ ∈ GQ (D.sp.X i)) (g) :
    rd F θ i hi β ψ y (γ * g) = rd F θ i hi β ψ y g := by
  have hc : chart F i hi β = endChart F i hi h := by rw [chart, dif_pos h]
  obtain ⟨Ψ, hΨ, e⟩ := ((F.val i hi h).Fi ψ).1 hψ
  rw [rd, hc, Chart.rd]
  have e' : (fun c z => ψ ((endChart F i hi h).inc c) ((endChart F i hi h).eY.symm z)) =
    fun c => Ψ ((endChart F i hi h).K.y c) := e.symm
  rw [e']
  exact rdS_left θ _ (rankN D i hi) _ _ hθ (endChart F i hi h).K.y_bij.2 Ψ hΨ.1 _ γ hγ g

theorem rdP_left (θ : InfFam D) (hθ : IsInfFam θ) (z : (D.mem u).P.Wrow) (hz : z ∈ (D.fm u).ptC) (y) (γ) (hγ : γ ∈ GQ D.sp.X') (g) :
    rdP F θ z y (γ * g) = rdP F θ z y g := by
  obtain ⟨Ψ, hΨ, e⟩ := (F.valP.ptC z).1 hz
  rw [rdP, ← e]
  exact rdS_left θ _ (rankP D) _ _ hθ F.clsP.y_bij.2 Ψ hΨ.1 _ γ hγ g

end GlobalTheory.AdForm.Model
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.LatticeFrames.TopLevExists
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Forms
open scoped TensorProduct

namespace GlobalTheory.Core.Rk.Top.Model

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {u : D.what₂.Word}

theorem unit_transfer {A B m n : Type} [CommRing A] [CommRing B] [Fintype m] [Fintype n] (e : m ≃ n) (s : A →+* B) (σ : A →+* A)
    (τ : B →+* B) (hs : ∀ x, s (σ x) = τ (s x)) (J : Matrix n n A) (J' : Matrix m m B) (hJ : ∀ a b, J' a b = s (J (e a) (e b)))
    (y : Matrix n n A) (g : Matrix m m B) (hg : ∀ a b, g a b = s (y (e a) (e b))) (hy : Formalism.UG.cT σ y * J * y = J) :
    Formalism.UG.cT τ g * J' * g = J' := by
  ext i j
  have := congrArg s (congrFun (congrFun hy (e i)) (e j))
  rw [hJ, ← this]
  simp only [Matrix.mul_apply, Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply, map_sum, map_mul, hg, hJ, hs]
  rw [← e.sum_comp]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← e.sum_comp]

theorem swap_inj : Function.Injective (Lev.swapAE D) :=
  (Algebra.TensorProduct.comm D.host.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.host.E).injective

theorem hasMat_mat {h : GA D D.sp.X'} {y y'} (h1 : HasMat h y) (h2 : HasMat h y') : y = y' := by
  apply Units.ext
  ext i j
  have a := h1.2 ((finCongr (rankP D)).symm i) ((finCongr (rankP D)).symm j)
  have b := h2.2 ((finCongr (rankP D)).symm i) ((finCongr (rankP D)).symm j)
  simp only [Equiv.apply_symm_apply] at a b
  rw [← a, ← b]

theorem hasMat_pt {h h' : GA D D.sp.X'} {y} (h1 : HasMat h y) (h2 : HasMat h' y) : h = h' := by
  refine GlobalTheory.UnitarySplit.ga_ext _ ?_ ?_
  · have a : infHom D.sp.X' h = 1 := h1.1
    have b : infHom D.sp.X' h' = 1 := h2.1
    rw [a, b]
  · apply Units.ext
    ext i j
    apply swap_inj
    exact (h1.2 i j).trans (h2.2 i j).symm

set_option maxHeartbeats 1000000 in

theorem hasMat_exists (y : Formalism.UG.UPts (sigD D) (gramP D) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) :
    ∃ h : GA D D.sp.X', HasMat h y.1 := by
  let e := finCongr (rankP D)
  let s := (Algebra.TensorProduct.comm D.host.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.host.E).symm
  let r := (Matrix.reindexAlgEquiv D.host.F (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F) e.symm)
  let g := Formalism.UG.bc s.toRingEquiv.toRingHom (Units.map r.toRingEquiv.toRingHom.toMonoidHom y.1)
  have hg : ∀ i j, g.1 i j = s (y.1.1 (e i) (e j)) := fun i j => rfl
  have hm : g ∈ Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig D.sp.X'.gram := by
    have hs : ∀ x, s (Formalism.UG.sigR (sigD D) _ x) = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ D.sp.cm.sig (s x) := by
      intro x
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul a x => rfl
      | add x y hx hy => simp only [map_add, hx, hy]
    have hy : Formalism.UG.cT (Formalism.UG.sigR (sigD D) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) y.1.1 *
        (gramP D).map (Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) * y.1.1 =
        (gramP D).map (Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) := y.2
    have hJ : ∀ a b, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.X'.gram a b =
        s.toRingEquiv.toRingHom (((gramP D).map (Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))) (e a) (e b)) :=
      fun a b => rfl
    have key := unit_transfer e s.toRingEquiv.toRingHom (Formalism.UG.sigR (sigD D) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))
      (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig) hs _ _ hJ y.1.1 g.1 hg hy
    exact key
  obtain ⟨k, k1, k2⟩ := GlobalTheory.UnitarySplit.ga_glue D.sp.X' 1 g (one_mem _) hm
  refine ⟨k, k1, fun i j => ?_⟩
  rw [k2]
  exact s.symm_apply_apply _

theorem hasMat_one : HasMat (1 : GA D D.sp.X') 1 := by
  refine ⟨one_mem _, fun i j => ?_⟩
  rw [map_one, map_one]
  simp [Matrix.one_apply, Fin.ext_iff]

open Classical in

theorem topLev_exists (K : ClsPTied u) : ∃ J χ, TopLev K J χ ∧ 1 ∈ J ∧ χ 1 = 1 ∧ ∀ κ : K.lev.U, ∃ h ∈ J, HasMat h κ.1 := by
  let χ : GA D D.sp.X' → ℂ := fun h => if hh : ∃ κ : K.lev.U, HasMat h κ.1 then star ((K.lev.chi hh.choose : ℂˣ) : ℂ) else 0
  have hχ : ∀ h (κ : K.lev.U), HasMat h κ.1 → χ h = star ((K.lev.chi κ : ℂˣ) : ℂ) := by
    intro h κ hk
    have hh : ∃ κ : K.lev.U, HasMat h κ.1 := ⟨κ, hk⟩
    simp only [χ, dif_pos hh]
    rw [show hh.choose = κ from Subtype.ext (hasMat_mat hh.choose_spec hk)]
  refine ⟨{h | ∃ κ : K.lev.U, HasMat h κ.1}, χ, ⟨fun _ => Iff.rfl, hχ⟩, ⟨1, hasMat_one⟩, ?_, fun κ => ?_⟩
  · rw [hχ 1 1 hasMat_one]; simp
  · obtain ⟨h, hh⟩ := hasMat_exists ⟨κ.1, ((K.lev.U_eq _).1 κ.2).1⟩
    exact ⟨h, ⟨κ, hh⟩, hh⟩

theorem isJ_smul {S : D.what₂.Tau → SPar} {M : DSModel D.sp.X' S} {j : SmT M →ₗ[ℂ] (FrP D → ℂ)} (h : IsJ u M j) {a : ℂ} (ha : a ≠ 0) :
    IsJ u M (a • j) := by
  refine ⟨fun x y hxy => h.inj (smul_right_injective _ ha hxy), ?_, fun τ g hg v w hw y y' hy => ?_⟩
  · rw [LinearMap.range_smul _ _ ha, h.range]
  · simp only [LinearMap.smul_apply, Pi.smul_apply]
    rw [h.eqv τ g hg v w hw y y' hy]

theorem multT_bot {V : HSp D} {S : D.what₂.Tau → SPar} (θ) (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ)
    (hχ : ∀ U : Subgroup (GA D V), IsOpen (U : Set (GA D V)) → ∃ k ∈ U, k ∈ GfC V ∧ k ∈ J ∧ χ k ≠ 1) :
    MultT θ M J χ = ⊥ := by
  have : Mult θ M J χ = ⊥ := by
    unfold Mult
    rw [Submodule.span_eq_bot]
    intro T hT
    ext v g
    obtain ⟨U, hU, hl⟩ := (hT.aut v).level
    obtain ⟨k, k1, k2, k3, k4⟩ := hχ U hU
    have e1 := hl k k1 k2 g
    rw [hT.lev v k k3 g] at e1
    have : (χ k - 1) * T v g = 0 := by rw [sub_mul, e1]; ring
    simpa [sub_eq_zero, k4] using this
  unfold MultT
  rw [this, Submodule.map_bot]

theorem period_zero {K : ClsPTied u} (V : ValPTied u K) {S : D.what₂.Tau → SPar} (θ) (M : DSModel D.sp.X' S)
    (j : SmT M →ₗ[ℂ] (FrP D → ℂ)) (J : Set (GA D D.sp.X')) (χ : GA D D.sp.X' → ℂ)
    (hχ : ∀ U : Subgroup (GA D D.sp.X'), IsOpen (U : Set (GA D D.sp.X')) → ∃ k ∈ U, k ∈ GfC D.sp.X' ∧ k ∈ J ∧ χ k ≠ 1)
    (eT : (D.mem u).P.Mt → MultT θ M J χ) (hf : TopFormula V M j fun F => (eT F).1) (F c v) :
    (D.mem u).P.period (V.eW.symm (by classical exact Pi.single c (j v))) F = 0 := by
  obtain ⟨h, hh⟩ := hasMat_exists (K.y c)
  have e := hf F c v h hh
  have z : (eT F).1 = 0 := by
    exact (Submodule.eq_bot_iff _).1 (multT_bot θ M J χ hχ) _ (eT F).2
  simp only [z, LinearMap.zero_apply, Pi.zero_apply] at e
  have hc : (Nat.card ((D.fm u).stabilizer₂ c) : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := (D.fm u).stabilizer₂ c)).ne'
  exact (mul_eq_zero.1 e.symm).resolve_left hc

theorem valC_ne_bot {ι : Type} [Fintype ι] {n : ℕ} (G : ι → Matrix (Fin n) (Fin n) ℂ) (lam : ι → DomWeight n) : ValC G lam ≠ ⊥ := by
  intro h
  have hm : fnOf G (shiftOf lam) 1 (ten fun τ => extremal ℂ n (lam τ)) ∈ ValC G lam :=
    ⟨_, Submodule.subset_span ⟨_, fun τ => Submodule.subset_span ⟨[], rfl⟩, rfl⟩, rfl⟩
  rw [h, Submodule.mem_bot] at hm
  have := congrFun hm ⟨fun _ => 1, fun _ => by simp⟩
  simp [fnOf, ten, extremal, Formalism.GradedWeylDivisibility.hw, Formalism.GradedWeylDivisibility.lpMinor, MvPolynomial.eval_rename, RingHom.map_det] at this
  have e : ∀ (x : ι) (s : ℕ) (h1 h2 : s ≤ n), ((Matrix.of fun p q : Fin s => (MvPolynomial.X (Fin.castLE h1 p, Fin.castLE h2 q) : MvPolynomial (Fin n × Fin n) ℂ)).map
      ⇑(MvPolynomial.eval ((fun x : ι × Fin n × Fin n => (1 : Matrix (Fin n) (Fin n) ℂ) x.2.1 x.2.2) ∘ Prod.mk x))) = 1 := by
    intro x s h1 h2
    ext p q
    simp [Matrix.one_apply]
  simp only [e, Matrix.det_one, one_pow, Finset.prod_const_one] at this
  exact one_ne_zero this

theorem not_isJ_zero {S : D.what₂.Tau → SPar} (M : DSModel D.sp.X' S) : ¬ IsJ u M 0 := fun h =>
  valC_ne_bot _ _ (h.range.symm.trans LinearMap.range_zero)

end GlobalTheory.Core.Rk.Top.Model

end
end

