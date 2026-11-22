import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.GlobalCharacterOfInputs
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0423
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicDoubleCosetDecomposition
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0397
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0446
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0429
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0447
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0338
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0441
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnlinkedGL.UnlinkedRealize
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0434

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousCoordinate
section
noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.G8

namespace GlobalTheory.CompanionTheory.CompIsoProof

theorem continuous_glMap {R S : Type} [CommRing R] [CommRing S] [TopologicalSpace R] [TopologicalSpace S]
    (f : R →+* S) (hf : Continuous f) (a : ℕ) :
    Continuous (GeneralLinearGroup.map f : GL (Fin a) R →* GL (Fin a) S) :=
  Continuous.units_map _ (continuous_id.matrix_map hf)

theorem continuous_cornerGL {R S : Type} [CommRing R] [CommRing S] [TopologicalSpace R] [TopologicalSpace S]
    [IsTopologicalRing S] (s : R →ₙ+* S) (hs : Continuous s) (a : ℕ) :
    Continuous (cornerGL a s) :=
  Continuous.units_map _ (continuous_const.add (continuous_id.matrix_map hs))

variable {E : Type} [Field E] {a : ℕ}

def glOf (y : InfinitePlace E → GL (Fin a) ℂ) : GL (Fin a) (Cinf E) where
  val := Matrix.of fun i j v => (y v).val i j
  inv := Matrix.of fun i j v => (y v).inv i j
  val_inv := by
    ext i j v
    have h := congrFun (congrFun (y v).val_inv i) j
    rw [Matrix.mul_apply, Matrix.one_apply] at h
    have e : (if i = j then (1 : Cinf E) else 0) v = if i = j then 1 else 0 := by split_ifs <;> rfl
    rw [Matrix.mul_apply, Finset.sum_apply, Matrix.one_apply, e]
    exact h
  inv_val := by
    ext i j v
    have h := congrFun (congrFun (y v).inv_val i) j
    rw [Matrix.mul_apply, Matrix.one_apply] at h
    have e : (if i = j then (1 : Cinf E) else 0) v = if i = j then 1 else 0 := by split_ifs <;> rfl
    rw [Matrix.mul_apply, Finset.sum_apply, Matrix.one_apply, e]
    exact h

theorem map_eval_glOf (y : InfinitePlace E → GL (Fin a) ℂ) (v : InfinitePlace E) :
    GeneralLinearGroup.map (Pi.evalRingHom (fun _ : InfinitePlace E => ℂ) v) (glOf y) = y v := by
  ext i j
  rfl

theorem continuous_glOf : Continuous (glOf : (InfinitePlace E → GL (Fin a) ℂ) → GL (Fin a) (Cinf E)) := by
  have h2 : Continuous fun x : GL (Fin a) ℂ => ((x⁻¹ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) :=
    (Units.continuous_iff.1 (continuous_id (X := GL (Fin a) ℂ))).2
  refine Units.continuous_iff.2 ⟨continuous_matrix fun i j => continuous_pi fun v => ?_,
    continuous_matrix fun i j => continuous_pi fun v => ?_⟩
  · exact (Units.continuous_val.matrix_elem i j).comp (continuous_apply v)
  · exact (h2.matrix_elem i j).comp (continuous_apply v)

variable [NumberField E]

theorem continuous_sFin : Continuous (sFin E) :=
  (continuous_const.prodMk continuous_id : Continuous fun x : Af E => ((0, x) : InfiniteAdeleRing E × Af E))

variable [IsTotallyComplex E]

theorem continuous_sInf : Continuous (sInf E) :=
  ((continuous_infEq E).prodMk continuous_const : Continuous fun x : Cinf E => ((infEq E x, 0) : InfiniteAdeleRing E × Af E))

theorem continuous_pInf : Continuous (pInf E) :=
  continuous_pi fun w =>
    (InfinitePlace.Completion.isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).continuous.comp
      ((continuous_apply w).comp continuous_fst)

theorem continuous_coordinate (v : InfinitePlace E) : Continuous (cV v : Ad E → ℂ) :=
  (continuous_apply v).comp continuous_pInf

theorem map_cV (v : InfinitePlace E) (g : GA E a) :
    GeneralLinearGroup.map (cV v) g =
      GeneralLinearGroup.map (Pi.evalRingHom (fun _ : InfinitePlace E => ℂ) v) (GeneralLinearGroup.map (pInf E) g) := by
  ext i j
  rfl

def parts (g : GA E a) : (InfinitePlace E → GL (Fin a) ℂ) × GL (Fin a) (Af E) :=
  (fun v => GeneralLinearGroup.map (cV v) g, GeneralLinearGroup.map (pFin E) g)

def glue (p : (InfinitePlace E → GL (Fin a) ℂ) × GL (Fin a) (Af E)) : GA E a :=
  infGL E a (glOf p.1) * finGL E a p.2

theorem glue_parts (g : GA E a) : glue (parts g) = g := by
  have h : glOf (fun v => GeneralLinearGroup.map (cV v) g) = GeneralLinearGroup.map (pInf E) g := by
    ext i j v
    rfl
  rw [glue, parts]
  simp only [h]
  exact infGL_mul_finGL g

theorem parts_glue (p : (InfinitePlace E → GL (Fin a) ℂ) × GL (Fin a) (Af E)) : parts (glue p) = p := by
  refine Prod.ext (funext fun v => ?_) ?_
  · change GeneralLinearGroup.map (cV v) (glue p) = p.1 v
    rw [map_cV, glue, map_mul, pInf_infGL, pInf_finGL, mul_one, map_eval_glOf]
  · change GeneralLinearGroup.map (pFin E) (glue p) = p.2
    rw [glue, map_mul, pFin_infGL, pFin_finGL, one_mul]

theorem continuous_parts : Continuous (parts : GA E a → _) :=
  (continuous_pi fun v => continuous_glMap (cV v) (continuous_coordinate v) a).prodMk
    (continuous_glMap (pFin E) continuous_snd a)

theorem continuous_glue : Continuous (glue : _ → GA E a) :=
  ((continuous_cornerGL (sInf E) continuous_sInf a).comp (continuous_glOf.comp continuous_fst)).mul
    ((continuous_cornerGL (sFin E) continuous_sFin a).comp continuous_snd)

theorem compIso : CompIso := by
  intro E _ _ _ a b
  refine ⟨{ toFun := comps
            invFun := fun p => (glue (fun v => (p.1 v).1, p.2.1), glue (fun v => (p.1 v).2, p.2.2))
            left_inv := fun x => Prod.ext (glue_parts x.1) (glue_parts x.2)
            right_inv := fun p => ?_
            map_mul' := fun x y => ?_
            continuous_toFun := ?_
            continuous_invFun := ?_ }, fun _ => rfl⟩
  · have h1 := fun v => congrFun (congrArg Prod.fst (parts_glue (a := a) (E := E) (fun v => (p.1 v).1, p.2.1))) v
    have h2 := fun v => congrFun (congrArg Prod.fst (parts_glue (a := b) (E := E) (fun v => (p.1 v).2, p.2.2))) v
    have h3 := congrArg Prod.snd (parts_glue (a := a) (E := E) (fun v => (p.1 v).1, p.2.1))
    have h4 := congrArg Prod.snd (parts_glue (a := b) (E := E) (fun v => (p.1 v).2, p.2.2))
    exact Prod.ext (funext fun v => Prod.ext (h1 v) (h2 v)) (Prod.ext h3 h4)
  · refine Prod.ext (funext fun v => Prod.ext ?_ ?_) (Prod.ext ?_ ?_) <;> exact map_mul _ _ _
  · have p1 : Continuous fun x : GA E a × GA E b => parts x.1 := continuous_parts.comp continuous_fst
    have p2 : Continuous fun x : GA E a × GA E b => parts x.2 := continuous_parts.comp continuous_snd
    exact (continuous_pi fun v => ((continuous_apply v).comp p1.fst).prodMk ((continuous_apply v).comp p2.fst)).prodMk
      (p1.snd.prodMk p2.snd)
  · have q1 : Continuous fun p : Gi E a b × Gf E a b => ((fun v => (p.1 v).1, p.2.1) :
        (InfinitePlace E → GL (Fin a) ℂ) × GL (Fin a) (Af E)) :=
      (continuous_pi fun v => ((continuous_apply v).comp continuous_fst).fst).prodMk continuous_snd.fst
    have q2 : Continuous fun p : Gi E a b × Gf E a b => ((fun v => (p.1 v).2, p.2.2) :
        (InfinitePlace E → GL (Fin b) ℂ) × GL (Fin b) (Af E)) :=
      (continuous_pi fun v => ((continuous_apply v).comp continuous_fst).snd).prodMk continuous_snd.snd
    exact (continuous_glue.comp q1).prodMk (continuous_glue.comp q2)

end GlobalTheory.CompanionTheory.CompIsoProof

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousOfRightInvariant
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host
open GlobalTheory.BCT
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.G8
open scoped Classical

namespace GlobalTheory.CompanionTheory.AdelCont

open PositivityTheory.Rg.Tf.Loc (twConj)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

theorem orbFn_mul_right (S : Set (Pl E)) (φ₁ φ₂ : ∀ w : Pl E, GLw a w × GLw b w → ℂ)
    (δ₁ : GL (Fin a) E) (δ₂ : GL (Fin b) E) (U : Subgroup (Gf E a b))
    (hU : ∀ u ∈ U, ∀ y, finFn S φ₁ φ₂ (u⁻¹ * y * thP E a b u) = finFn S φ₁ φ₂ y)
    (x u : Gf E a b) (hu : u ∈ U) : orbFn S φ₁ φ₂ δ₁ δ₂ (x * u) = orbFn S φ₁ φ₂ δ₁ δ₂ x := by
  unfold orbFn
  rw [← hU u hu (x⁻¹ * (ratF E a δ₁, ratF E b δ₂) * thP E a b x), map_mul]
  congr 1
  group

theorem continuous_of_right_invariant {G X : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [TopologicalSpace X] (f : G → X) (U : Subgroup G) (hUo : IsOpen (U : Set G))
    (hf : ∀ x, ∀ u ∈ U, f (x * u) = f x) : Continuous f := by
  have : IsLocallyConstant f := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    have hmem : (x⁻¹ * ·) ⁻¹' (U : Set G) ∈ nhds x := by
      apply (continuous_const.mul continuous_id).continuousAt.preimage_mem_nhds
      apply hUo.mem_nhds
      simp [U.one_mem]
    filter_upwards [hmem] with y hy
    have := hf x (x⁻¹ * y) hy
    simpa using this
  exact this.continuous

theorem continuous_twConj {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (θ : Monoid.End G) (hθ : Continuous θ) (δ : G) : Continuous fun g : G => twConj θ g δ := by
  unfold twConj
  exact (continuous_inv.mul continuous_const).mul hθ

theorem adelContOf : AdelContOf := by
  intro hEq hFin hComp hTopo E _ _ _ hUnr a b S u₁ u₂ h₁ h₂ ψ φ₁ φ₂ hψ t₁ t₂ d₁ d₂
  obtain ⟨e, he⟩ := hComp E a b
  have hc : Continuous (comps : GA E a × GA E b → Gi E a b × Gf E a b) := by
    have : (comps : GA E a × GA E b → Gi E a b × Gf E a b) = e := funext fun x => (he x).symm
    rw [this]; exact e.continuous
  have hθa : Continuous (thetaR (starRingEnd ℂ) a) := (hTopo E a).2.2.2.2.2
  have hθb : Continuous (thetaR (starRingEnd ℂ) b) := (hTopo E b).2.2.2.2.2
  obtain ⟨U, hUo, hU⟩ := hFin E hUnr a b S φ₁ φ₂ t₁ t₂
  have hfin : Continuous (orbFn S φ₁ φ₂ (d₁ * u₁⁻¹) (d₂ * u₂⁻¹)) :=
    continuous_of_right_invariant _ U hUo fun x u hu => orbFn_mul_right S φ₁ φ₂ _ _ U hU x u hu
  have hrw : (fun x : GA E a × GA E b =>
      adel S u₁ u₂ ψ φ₁ φ₂ (twConj (thetaA E a) x.1 (ratGL E a d₁), twConj (thetaA E b) x.2 (ratGL E b d₂))) =
      fun x => (∏ v, ψ v (twConj (thetaR (starRingEnd ℂ) a) ((comps x).1 v).1 (GeneralLinearGroup.map v.embedding d₁),
        twConj (thetaR (starRingEnd ℂ) b) ((comps x).1 v).2 (GeneralLinearGroup.map v.embedding d₂))) *
      orbFn S φ₁ φ₂ (d₁ * u₁⁻¹) (d₂ * u₂⁻¹) (comps x).2 :=
    funext fun x => hEq E a b S u₁ u₂ h₁ h₂ ψ φ₁ φ₂ d₁ d₂ x
  rw [hrw]
  refine Continuous.mul (continuous_finsetProd _ fun v _ => (hψ v).comp ?_) (hfin.comp (continuous_snd.comp hc))
  have hv : Continuous fun x : GA E a × GA E b => (comps x).1 v :=
    (continuous_apply v).comp (continuous_fst.comp hc)
  exact ((continuous_twConj _ hθa _).comp (continuous_fst.comp hv)).prodMk
    ((continuous_twConj _ hθb _).comp (continuous_snd.comp hv))

end GlobalTheory.CompanionTheory.AdelCont

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousOnRowM
section
noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZPhiPG.Chart

open GlobalTheory.CompanionTheory.BZPhiPG.Cells

section Alg

variable {k : Type} [Field k]

def rowM {ι : Type} [DecidableEq ι] (ρ : ι → k) (c j : ι) : Matrix ι ι k :=
  ((1 : Matrix ι ι k).updateRow c ρ).submatrix (Equiv.swap c j) id

theorem rowM_det_ne {ι : Type} [Fintype ι] [DecidableEq ι] (ρ : ι → k) (c j : ι) (hc : ρ c ≠ 0) :
    (rowM ρ c j).det ≠ 0 := by
  have hT : ((1 : Matrix ι ι k).updateRow c ρ).det = ρ c := by
    have h := Matrix.cramer_transpose_apply (1 : Matrix ι ι k) ρ c
    rw [Matrix.transpose_one, Matrix.cramer_one] at h
    simpa using h.symm
  have h := Matrix.det_permute (Equiv.swap c j) ((1 : Matrix ι ι k).updateRow c ρ)
  have h2 : (rowM ρ c j).det = _ := h
  rw [h2, hT]
  refine mul_ne_zero ?_ hc
  rcases Int.units_eq_one_or (Equiv.Perm.sign (Equiv.swap c j)) with e | e <;> simp [e]

theorem rowM_row {ι : Type} [DecidableEq ι] (ρ : ι → k) (c j : ι) : rowM ρ c j j = ρ := by
  ext x
  show ((1 : Matrix ι ι k).updateRow c ρ) (Equiv.swap c j j) x = ρ x
  simp

theorem rowM_zero {ι : Type} [DecidableEq ι] (s : ι → Prop) (ρ : ι → k) (c j : ι) (hc : s c) (hj : s j)
    (r x : ι) (hr : ¬ s r) (hx : s x) : rowM ρ c j r x = 0 := by
  have hrc : r ≠ c := fun e => hr (e ▸ hc)
  have hrj : r ≠ j := fun e => hr (e ▸ hj)
  have hrx : r ≠ x := fun e => hr (e ▸ hx)
  show ((1 : Matrix ι ι k).updateRow c ρ) (Equiv.swap c j r) x = 0
  rw [Equiv.swap_apply_of_ne_of_ne hrc hrj, Matrix.updateRow_ne hrc, Matrix.one_apply_ne hrx]

open Classical in

def rowB {ι : Type} [Fintype ι] [DecidableEq ι] (ρ : ι → k) (c j : ι) : GL ι k :=
  if h : (rowM ρ c j).det ≠ 0 then Matrix.GeneralLinearGroup.mkOfDetNeZero _ h else 1

theorem rowB_val {ι : Type} [Fintype ι] [DecidableEq ι] (ρ : ι → k) (c j : ι) (hc : ρ c ≠ 0) :
    (rowB ρ c j).val = rowM ρ c j := by
  rw [rowB, dif_pos (rowM_det_ne ρ c j hc)]
  rfl

end Alg

section Top

variable {k : Type} [Field k] [TopologicalSpace k] [IsTopologicalDivisionRing k]

theorem continuousOn_GL {X ι : Type} [TopologicalSpace X] [Fintype ι] [DecidableEq ι] (f : X → GL ι k) (V : Set X)
    (hf : ContinuousOn (fun x => (f x).val) V) : ContinuousOn f V := by
  rw [continuousOn_iff_continuous_restrict] at hf ⊢
  refine Units.continuous_iff.2 ⟨hf, ?_⟩
  have hdet : Continuous fun x : V => ((f x).val).det := hf.matrix_det
  have hne : ∀ x : V, ((f x).val).det ≠ 0 := fun x => (Matrix.GeneralLinearGroup.det (f x)).ne_zero
  have e : (fun x : V => (((f x)⁻¹ : GL ι k)).val) = fun x : V => (((f x).val).det)⁻¹ • ((f x).val).adjugate := by
    funext x
    rw [Matrix.coe_units_inv, Matrix.inv_def, Ring.inverse_eq_inv']
  show Continuous (fun x : V => (((f x)⁻¹ : GL ι k)).val)
  rw [e]
  exact (hdet.inv₀ hne).smul hf.matrix_adjugate

theorem continuousOn_rowM {X ι : Type} [TopologicalSpace X] [DecidableEq ι] (ρ : X → ι → k) (c j : ι)
    (hρ : Continuous ρ) : Continuous fun x => rowM (ρ x) c j := by
  refine continuous_matrix fun a b => ?_
  show Continuous fun x => ((1 : Matrix ι ι k).updateRow c (ρ x)) (Equiv.swap c j a) b
  by_cases h : Equiv.swap c j a = c
  · simp only [h, Matrix.updateRow_self]
    exact (continuous_apply b).comp hρ
  · simp only [Matrix.updateRow_ne h]
    exact continuous_const

end Top

section Group

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem core' (i t : ℕ) (p : Mir k ((i + 1) + t + 1)) (X B : GL (Fin ((i + 1) + t + 1)) k) (j : Fin ((i + 1) + t + 1))
    (hX : X.val j = eLast k ((i + 1) + t))
    (hBj : B.val j = (mirabolicProjection k _ p⁻¹ : GL (Fin ((i + 1) + t + 1)) k).val (Fin.last ((i + 1) + t)))
    (hB : ∀ r x : Fin ((i + 1) + t + 1), ¬ r.val < i + 1 → x.val < i + 1 → B.val r x = 0) :
    ∃ hM : (X⁻¹ * B * mirabolicProjection k _ p) ∈ Mir k ((i + 1) + t), ∃ h ∈ HPG k (i + 1) (t + 1), ∃ (d : Fin (t + 1) → k),
      p = h * dEmb k i t d * levi k _ X * sEmb k ((i + 1) + t) ⟨_, hM⟩ := by
  set g : GL (Fin ((i + 1) + t + 1)) k := mirabolicProjection k _ p with hg
  have hginv : mirabolicProjection k _ p⁻¹ = g⁻¹ := map_inv _ _
  rw [hginv] at hBj
  have hM : (X⁻¹ * B * g) ∈ Mir k ((i + 1) + t) := by
    have h1 : (g⁻¹ * (B⁻¹ * X)) ∈ Mir k ((i + 1) + t) := by
      rw [mem_Mir_iff, Units.val_mul, Matrix.mul_apply_eq_vecMul, ← hBj, ← Matrix.mul_apply_eq_vecMul, ← Units.val_mul,
        mul_inv_cancel_left, hX]
    have h2 := (Mir k ((i + 1) + t)).inv_mem h1
    simpa [mul_assoc] using h2
  let v : Fin ((i + 1) + (t + 1)) → k := fun r =>
    (p : GL (Fin ((i + 1) + t + 1 + 1)) k).val (Fin.castSucc r) (Fin.last _)
  let v' : Fin ((i + 1) + (t + 1)) → k := B.val.mulVec v
  let a : Fin ((i + 1) + (t + 1)) → k := Fin.append (fun x => v' (Fin.castAdd (t + 1) x)) (0 : Fin (t + 1) → k)
  let d : Fin (t + 1) → k := fun x => v' (Fin.natAdd (i + 1) x)
  let b : Fin ((i + 1) + (t + 1)) → k := Fin.append (0 : Fin (i + 1) → k) d
  have hsum : a + b = v' := by
    funext x
    induction x using Fin.addCases with
    | left x => simp [a, b]
    | right x => simp [a, b, d]
  let ua : Mir k ((i + 1) + t + 1) := ⟨unip k ((i + 1) + (t + 1)) (Multiplicative.ofAdd a), MirU_le_Mir k _ ⟨_, rfl⟩⟩
  have hua : ua ∈ HPG k (i + 1) (t + 1) := by
    refine mem_HPG_of (I := i + 1) (T := t + 1) ua ?_ ?_
    · intro x y
      refine unip_castSucc_castSucc _ a _ _ ?_
      intro e
      have := congrArg Fin.val e
      simp only at this
      omega
    · intro x
      refine (unip_apply_castSucc_last k _ _ _).trans ?_
      show a (Fin.natAdd (i + 1) x) = 0
      simp [a]
  have hlB : levi k _ B⁻¹ ∈ HPG k (i + 1) (t + 1) := by
    have : levi k _ B ∈ HPG k (i + 1) (t + 1) := by
      refine mem_HPG_of (I := i + 1) (T := t + 1) _ ?_ ?_
      · intro x y
        refine (glEmb_castSucc_castSucc _ B _ _).trans ?_
        exact hB _ _ (by simp; omega) (by simp; omega)
      · intro x
        exact glEmb_castSucc_last _ B _
    rw [map_inv]
    exact (HPG k (i + 1) (t + 1)).inv_mem this
  refine ⟨hM, levi k _ B⁻¹ * ua, (HPG k (i + 1) (t + 1)).mul_mem hlB hua, d, ?_⟩
  apply Subtype.ext
  have hp : (p : GL (Fin ((i + 1) + t + 1 + 1)) k) =
      unip k ((i + 1) + t + 1) (Multiplicative.ofAdd v) * glEmb k _ g := eq_unip_glEmb p
  have e1 : unip k ((i + 1) + t + 1) (Multiplicative.ofAdd a) *
      unip k ((i + 1) + t + 1) (Multiplicative.ofAdd b) =
      unip k ((i + 1) + t + 1) (Multiplicative.ofAdd v') := by
    rw [← map_mul, ← ofAdd_add, hsum]
  have e2 : glEmb k _ B * unip k ((i + 1) + t + 1) (Multiplicative.ofAdd v) =
      unip k ((i + 1) + t + 1) (Multiplicative.ofAdd v') * glEmb k _ B := glEmb_mul_unip' k _ B _
  have e3 : glEmb k _ X * glEmb k _ (X⁻¹ * B * g) = glEmb k _ B * glEmb k _ g := by
    rw [← map_mul, ← map_mul]
    congr 1
    group
  show (p : GL (Fin ((i + 1) + t + 1 + 1)) k) = glEmb k _ B⁻¹ * unip k ((i + 1) + t + 1) (Multiplicative.ofAdd a) *
      unip k ((i + 1) + t + 1) (Multiplicative.ofAdd b) *
      glEmb k _ X * glEmb k _ (X⁻¹ * B * g)
  calc (p : GL (Fin ((i + 1) + t + 1 + 1)) k)
      = (glEmb k _ B)⁻¹ * (glEmb k _ B * unip k ((i + 1) + t + 1) (Multiplicative.ofAdd v)) * glEmb k _ g := by
        rw [hp]; group
    _ = (glEmb k _ B)⁻¹ * unip k ((i + 1) + t + 1) (Multiplicative.ofAdd v') * (glEmb k _ B * glEmb k _ g) := by
        rw [e2]; simp only [mul_assoc]
    _ = _ := by
        rw [← e3, ← e1, map_inv]; simp only [mul_assoc]

end Group

theorem chart :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ)
      (p₀ : Mir k ((i + 1) + t + 1)), p₀ ∉ Cl k i t →
  ∃ V ∈ nhds p₀, ∃ μ : Mir k ((i + 1) + t + 1) → Mir k ((i + 1) + t), ContinuousOn μ V ∧
    ∀ p ∈ V, ∃ h ∈ HPG k (i + 1) (t + 1), ∃ d : Fin (t + 1) → k,
      p = h * dEmb k i t d * wEl k i t * sEmb k ((i + 1) + t) (μ p) := by
  classical
  intro k _ _ _ _ i t p₀ h₀
  have hp' : ¬ _ := fun h => h₀ ((Cl_iff i t p₀).2 h)
  push_neg at hp'
  obtain ⟨c, hcs, hc⟩ := hp'
  have hj : (piPerm i t (Fin.last ((i + 1) + t))).val < i + 1 := by rw [piPerm_last_val]; omega
  set j := piPerm i t (Fin.last ((i + 1) + t)) with hjdef
  let ρ : Mir k ((i + 1) + t + 1) → Fin ((i + 1) + t + 1) → k := fun p =>
    (mirabolicProjection k _ p⁻¹ : GL (Fin ((i + 1) + t + 1)) k).val (Fin.last ((i + 1) + t))
  have hG : Continuous fun p : Mir k ((i + 1) + t + 1) => mirabolicProjection k _ p :=
    GlobalTheory.CompanionTheory.BZMirFun.continuous_mirProj k _
  have hρ : Continuous ρ := by
    have hv : Continuous fun p : Mir k ((i + 1) + t + 1) =>
        ((mirabolicProjection k _ p⁻¹ : GL (Fin ((i + 1) + t + 1)) k) : Matrix (Fin ((i + 1) + t + 1)) (Fin ((i + 1) + t + 1)) k) :=
      Units.continuous_val.comp (hG.comp continuous_inv)
    exact continuous_pi fun x => hv.matrix_elem _ _
  let V : Set (Mir k ((i + 1) + t + 1)) := {p | ρ p c ≠ 0}
  have hV : IsOpen V := isOpen_ne_fun ((continuous_apply c).comp hρ) continuous_const
  let W : Mir k ((i + 1) + t + 1) → GL (Fin ((i + 1) + t + 1)) k := fun p =>
    (wGL k i t)⁻¹ * rowB (ρ p) c j * mirabolicProjection k _ p
  let μ : Mir k ((i + 1) + t + 1) → Mir k ((i + 1) + t) := fun p =>
    if h : W p ∈ Mir k ((i + 1) + t) then ⟨W p, h⟩ else 1
  have key : ∀ p ∈ V, ∃ hM : W p ∈ Mir k ((i + 1) + t), ∃ h ∈ HPG k (i + 1) (t + 1), ∃ d : Fin (t + 1) → k,
      p = h * dEmb k i t d * levi k _ (wGL k i t) * sEmb k ((i + 1) + t) ⟨_, hM⟩ := by
    intro p hp
    refine core' i t p (wGL k i t) (rowB (ρ p) c j) j (wGL_row i t) ?_ ?_
    · rw [rowB_val _ _ _ hp, rowM_row]
    · intro r x hr hx
      rw [rowB_val _ _ _ hp]
      exact rowM_zero (fun x : Fin ((i + 1) + t + 1) => x.val < i + 1) _ c j hcs hj r x hr hx
  refine ⟨V, hV.mem_nhds hc, μ, ?_, ?_⟩
  · have hB : ContinuousOn (fun p => rowB (ρ p) c j) V := by
      refine continuousOn_GL _ _ ?_
      refine (continuousOn_rowM ρ c j hρ).continuousOn.congr ?_
      intro p hp
      exact rowB_val _ _ _ hp
    have hW : ContinuousOn W V :=
      (continuousOn_const.mul hB).mul hG.continuousOn
    refine (Topology.IsEmbedding.subtypeVal.isInducing.continuousOn_iff).2 ?_
    refine hW.congr ?_
    intro p hp
    obtain ⟨hM, -⟩ := key p hp
    show ((μ p : Mir k ((i + 1) + t)) : GL _ k) = W p
    simp only [μ, dif_pos hM]
  · intro p hp
    obtain ⟨hM, h, hh, d, e⟩ := key p hp
    refine ⟨h, hh, d, ?_⟩
    have hμ : μ p = ⟨W p, hM⟩ := dif_pos hM
    rw [hμ]
    exact e

end GlobalTheory.CompanionTheory.BZPhiPG.Chart

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousShiftedOrbitMap
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG GlobalTheory.CompanionTheory.BZPhiPG.OntoO Topology
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZPhiPG.OntoO

theorem continuous_castM (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {a b : ℕ} (h : a = b) : Continuous (castM k h) := by
  subst h
  exact continuous_id

theorem continuous_sO : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (i t : ℕ), Continuous (sO k i t) := by
  intro k _ _ _ _ i t
  exact (GlobalTheory.CompanionTheory.BZPhiPG.EcSmooth.continuous_sEmb k ((i + 1) + t)).comp (continuous_castM k _)

end GlobalTheory.CompanionTheory.BZPhiPG.OntoO
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CountIsInvInvariant
section
noncomputable section

open MeasureTheory
open scoped ENNReal

namespace GlobalTheory.CompanionTheory.QuotNorm

theorem count_isInvInvariant {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
    [MeasurableSingletonClass G] (H : Subgroup G) : (Measure.count : Measure H).IsInvInvariant := by
  have hinv : MeasurableInv H := ⟨(measurable_subtype_coe.inv).subtype_mk⟩
  refine ⟨?_⟩
  ext s hs
  rw [Measure.inv_apply, Measure.count_apply hs, Measure.count_apply hs.inv, ← Set.image_inv_eq_inv]
  exact congrArg ((↑) : ℕ∞ → ℝ≥0∞) (inv_injective.encard_image s)

theorem qIndep : PositivityTheory.Rg.BcB.G8.QIndep := by
  intro G _ _ _ _ _ μ _ _ H _ F ρ hF hFH hρ
  have := count_isInvInvariant H
  exact quotIntegral_eq (μG := μ) hF hFH hρ

end GlobalTheory.CompanionTheory.QuotNorm
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalSupportRealisedByProductStatement
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.RgGu
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspidal_support_realised_by_product : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V) (s : Multiset (IrrGL k)), HasSupport π s → ∃ (h : ℕ) (x : Fin h → IrrGL k) (hd : ∑ a, (x a).1 = N), Finset.univ.val.map x = s ∧ (∀ a, (x a).IsCusp) ∧ IsSubquotient π (prodIrr x hd) := by
  first | exact @GlobalTheory.CompanionTheory.GenSupp.hasSupport_std | exact GlobalTheory.CompanionTheory.GenSupp.hasSupport_std | (intros; apply GlobalTheory.CompanionTheory.GenSupp.hasSupport_std <;> assumption)
end

