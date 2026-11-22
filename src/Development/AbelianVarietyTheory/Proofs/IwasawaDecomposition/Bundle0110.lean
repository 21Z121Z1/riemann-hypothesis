import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0003
import Formalism.LocalRingCardinality.Bundle0007
import Formalism.LocalRingCardinality.Bundle0003
import Formalism.LocalRingCardinality.Lemmas
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0212
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0098
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0099
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0103
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalToGlobal.Divisibility.Tuples
import Formalism.LocalToGlobal.UnitaryNorms.Bundle0006
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0104
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0101
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DuStarPos
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SpreadLe
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0004
import Formalism.SharpRestriction.InertJacobiLevels.HostFam

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LinearIndependentSemilinearOfBasis
section
noncomputable section

namespace GlobalTheory.Mem

open Formalism.BasicNotions NumberField IsDedekindDomain

theorem linearIndependent_semilinear_of_basis {K : Type} [Field K] (e : K →+* ℂ) {V : Type} [AddCommGroup V]
    [Module K V] {W : Type} [AddCommGroup W] [Module ℂ W] (j : V →ₛₗ[e] W) {ι κ : Type}
    (b : Module.Basis ι K V) (hb : LinearIndependent ℂ (fun i => j (b i))) (v : κ → V)
    (hv : LinearIndependent K v) : LinearIndependent ℂ (fun i => j (v i)) := by
  classical
  set S : Submodule ℂ W := Submodule.span ℂ (Set.range fun i => j (b i)) with hS
  have hmem : ∀ x, j x ∈ S := by
    intro x
    have hx : x ∈ Submodule.span K (Set.range b) := by rw [b.span_eq]; trivial
    induction hx using Submodule.span_induction with
    | mem y hy => obtain ⟨i, rfl⟩ := hy; exact Submodule.subset_span ⟨i, rfl⟩
    | zero => simp
    | add y z _ _ hy hz => rw [map_add]; exact S.add_mem hy hz
    | smul a y _ hy => rw [map_smulₛₗ]; exact S.smul_mem _ hy
  let j' : V →ₛₗ[e] S := j.codRestrict S hmem
  have h1 : LinearIndependent ℂ (fun i => j' (b i)) :=
    LinearIndependent.of_comp S.subtype hb
  have h2 : Submodule.span ℂ (Set.range fun i => j' (b i)) = ⊤ := by
    apply Submodule.map_injective_of_injective S.injective_subtype
    rw [Submodule.map_span, ← Set.range_comp, Submodule.map_top, Submodule.range_subtype]
    rfl
  let b' := Module.Basis.extend (hv.linearIndepOn_id)
  have h3 := (GlobalTheory.semilinear_basis_image_indep_of_basis K e V S j' ι _ b b' ⟨h1, h2⟩).1
  have h4 := h3.map' S.subtype S.ker_subtype
  let f : κ → (hv.linearIndepOn_id).extend (Set.subset_univ _) := fun i =>
    ⟨v i, (hv.linearIndepOn_id).subset_extend _ ⟨i, rfl⟩⟩
  have hf : Function.Injective f := fun a c h => hv.injective (congrArg Subtype.val h)
  have h5 := h4.comp f hf
  have h6 : (fun i => j (v i)) = (⇑S.subtype ∘ fun i => j' (b' i)) ∘ f := by
    funext i
    simp [b', f, j', Module.Basis.extend_apply_self]
  rw [h6]
  exact h5

def coordForm {K : Type} [Field K] (e : K →+* ℂ) {W : Type} [AddCommGroup W] [Module ℂ W] {n : ℕ}
    (c : Fin n → W) : (Fin n → K) →ₛₗ[e] W where
  toFun x := ∑ i, e (x i) • c i
  map_add' x y := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' a x := by simp [Finset.smul_sum, mul_smul]

theorem coordForm_basisFun {K : Type} [Field K] (e : K →+* ℂ) {W : Type} [AddCommGroup W] [Module ℂ W] {n : ℕ}
    (c : Fin n → W) (i : Fin n) : coordForm e c (Pi.basisFun K (Fin n) i) = c i := by
  classical
  show ∑ k, e (Pi.basisFun K (Fin n) i k) • c k = c i
  rw [Finset.sum_eq_single i]
  · simp
  · intro k _ hk; simp [hk]
  · simp

def ramForm {B : Base} {C : Cols B} (W : RowsRest B C) (u : B.Word) :
    (C.fm u).ramSub →ₛₗ[B.embLL] W.Mu u where
  toFun x := (W.eMu u).symm ⟨(C.fm u).emb 0 x, x.2⟩
  map_add' x y := by
    rw [← map_add]; congr 1; ext1; simp
  map_smul' a x := by
    rw [← map_smul]; congr 1; ext1; simp [map_smulₛₗ]

theorem eMu_ramForm {B : Base} {C : Cols B} (W : RowsRest B C) (u : B.Word) (x : (C.fm u).ramSub) :
    ((W.eMu u (ramForm W u x) : (C.mem u).A.Mram) : (C.mem u).C.cls 0 → (C.mem u).C.Y 0 → ℂ) =
      (C.fm u).emb 0 x := by
  show ((W.eMu u ((W.eMu u).symm _) : (C.mem u).A.Mram) : (C.mem u).C.cls 0 → (C.mem u).C.Y 0 → ℂ) = _
  rw [LinearEquiv.apply_symm_apply]

theorem ramForm_basis {B : Base} {C : Cols B} (W : RowsRest B C) (u : B.Word) {κ : Type}
    (b : Module.Basis κ B.LL (C.fm u).ramSub) :
    LinearIndependent ℂ (fun i => ramForm W u (b i)) ∧
      Submodule.span ℂ (Set.range (fun i => ramForm W u (b i))) = ⊤ := by
  let g : W.Mu u →ₗ[ℂ] ((C.mem u).C.cls 0 → (C.mem u).C.Y 0 → ℂ) :=
    (C.mem u).A.Mram.subtype ∘ₗ (W.eMu u).toLinearMap
  have hg : ∀ x, g (ramForm W u x) = (C.fm u).emb 0 x := eMu_ramForm W u
  have hginj : Function.Injective g := (C.mem u).A.Mram.injective_subtype.comp (W.eMu u).injective
  constructor
  · apply LinearIndependent.of_comp g
    have := linearIndependent_semilinear_of_basis B.embLL ((C.fm u).emb 0) ((C.fm u).lat 0).b
      ((C.fm u).emb_basis 0).1 (fun i => ((b i : (C.fm u).ramSub) : ((C.fm u).lat 0).V))
      (b.linearIndependent.map' (C.fm u).ramSub.subtype (Submodule.ker_subtype _))
    have h6 : (⇑g ∘ fun i => ramForm W u (b i)) =
        fun i => (C.fm u).emb 0 ((b i : (C.fm u).ramSub) : ((C.fm u).lat 0).V) := funext fun i => hg _
    rw [h6]
    exact this
  · set S := Submodule.span ℂ (Set.range (fun i => ramForm W u (b i))) with hS
    have hmem : ∀ x, ramForm W u x ∈ S := by
      intro x
      have hx : x ∈ Submodule.span B.LL (Set.range b) := by rw [b.span_eq]; trivial
      induction hx using Submodule.span_induction with
      | mem y hy => obtain ⟨i, rfl⟩ := hy; exact Submodule.subset_span ⟨i, rfl⟩
      | zero => simp
      | add y z _ _ hy hz => rw [map_add]; exact S.add_mem hy hz
      | smul a y _ hy => rw [map_smulₛₗ]; exact S.smul_mem _ hy
    rw [eq_top_iff]
    intro φ _
    have h1 : g φ ∈ (C.mem u).A.Mram := (W.eMu u φ).2
    rw [← GlobalTheory.RamRational.span_ramSub_cols B C u] at h1
    have h2 : Submodule.span ℂ ((C.fm u).emb 0 '' ((C.fm u).ramSub : Set ((C.fm u).lat 0).V)) ≤ S.map g := by
      rw [Submodule.span_le]
      rintro _ ⟨x, hx, rfl⟩
      exact ⟨_, hmem ⟨x, hx⟩, hg _⟩
    obtain ⟨ψ, hψ, hψ'⟩ := h2 h1
    rwa [← hginj hψ']

theorem exists_divStage (B : Base) (C : Cols B) (W : RowsRest B C) (n : ℕ) (c : Module.Basis (Fin n) ℂ W.EE)
    (Xo : InfinitePlace B.LL → Matrix (Fin n) (Fin n) ℂ) (hXo : ∀ v, IsUnit (Xo v).det)
    (Lr : Submodule (𝓞 B.LL) (Fin n → B.LL)) (Ln : ∀ u, Submodule (𝓞 B.LL) ((C.fm u).lat 0).V)
    (Bk : ∀ u, ((C.fm u).lat 0).V →ₗ[B.LL] Module.Dual B.LL (Fin n → B.LL)) (h : B.Word → ℝ) (etaF : ℝ) :
    ∃ (V : DivStage B C W) (e : V.div.RR.V ≃ₗ[B.LL] (Fin n → B.LL)),
      (∀ x, V.jEE x = ∑ i, B.embLL (e x i) • c i) ∧ (∀ x, x ∈ V.div.RR.L ↔ e x ∈ Lr) ∧
      (∀ v, v ≠ InfinitePlace.mk B.embLL → ∀ x, Formalism.HermitianLatticesTheory.normAt V.div.RR.b V.div.RR.X v x =
        Formalism.HermitianLatticesTheory.normAt (Pi.basisFun B.LL (Fin n)) Xo v (e x)) ∧
      (∀ u x, x ∈ (V.div.Nu u).L ↔ V.nuIn u x ∈ Ln u) ∧
      (∀ u φ x, V.div.Bk u φ x = Bk u (V.nuIn u φ) (e x)) ∧ V.div.h = h ∧ V.div.etaF = etaF ∧
      V.div.HH = sFrame V.div.Nu V.div.h + V.div.RR.muMax := by
  classical
  obtain ⟨X0, hX0, hX0n⟩ := GlobalTheory.exists_frames_normAt_eq_norm B.LL B.embLL W.EE n c Lr
  choose m bN XN hXN hXNn using fun u : B.Word =>
    GlobalTheory.Mem.exists_restricted_frames B.LL ((C.fm u).lat 0) (C.fm u).ramSub ⊥ ((C.fm u).lat_good 0).1
  let X : InfinitePlace B.LL → Matrix (Fin n) (Fin n) ℂ := fun v =>
    if v = InfinitePlace.mk B.embLL then X0 v else Xo v
  let RR : HLat B.LL :=
    { V := Fin n → B.LL, ι := Fin n, b := Pi.basisFun B.LL (Fin n), X := X, L := Lr }
  let Nu : B.Word → HLat B.LL := fun u =>
    { V := (C.fm u).ramSub, ι := Fin (m u), b := bN u, X := XN u,
      L := (Ln u).comap ((C.fm u).ramSub.subtype.restrictScalars (𝓞 B.LL)) }
  let D : DivData B.LL B.Word :=
    { RR := RR, Nu := Nu, Bk := fun u => (Bk u) ∘ₗ (C.fm u).ramSub.subtype, h := h,
      HH := sFrame Nu h + RR.muMax, HH_ge := le_rfl, etaF := etaF, Dall := W.Dall, delP := W.delp,
      delP_le_one := W.delp_le_one }
  let V : DivStage B C W :=
    { div := D
      div_good := ⟨fun v => by
        show IsUnit (if v = InfinitePlace.mk B.embLL then X0 v else Xo v).det
        split_ifs
        · exact hX0 v
        · exact hXo v, fun u v => hXN u v⟩
      jEE := coordForm B.embLL c
      jEE_basis := by
        have : (fun i => coordForm B.embLL c (Pi.basisFun B.LL (Fin n) i)) = c :=
          funext (coordForm_basisFun B.embLL c)
        show LinearIndependent ℂ (fun i => coordForm B.embLL c (Pi.basisFun B.LL (Fin n) i)) ∧
          Submodule.span ℂ (Set.range (fun i => coordForm B.embLL c (Pi.basisFun B.LL (Fin n) i))) = ⊤
        rw [this]
        exact ⟨c.linearIndependent, c.span_eq⟩
      jN := ramForm W
      jN_basis := fun u => ramForm_basis W u (bN u)
      Dall_eq := rfl
      delP_eq := rfl
      nuIn := fun u => (C.fm u).ramSub.subtype
      nuIn_inj := fun u => (C.fm u).ramSub.injective_subtype
      nuIn_range := fun u => Submodule.range_subtype _
      nuIn_jN := fun u x => eMu_ramForm W u x
      nuIn_norm := fun u v x => hXNn u v x
      jEE_norm := fun x => by
        refine Eq.trans ?_ (hX0n x)
        show Formalism.HermitianLatticesTheory.normAt (Pi.basisFun B.LL (Fin n)) X _ x = _
        simp only [Formalism.HermitianLatticesTheory.normAt, Formalism.HermitianLatticesTheory.fcoord, X, if_true] }
  refine ⟨V, LinearEquiv.refl _ _, fun x => rfl, fun x => Iff.rfl, fun v hv x => ?_, fun u x => Iff.rfl,
    fun u φ x => rfl, rfl, rfl, rfl⟩
  show Formalism.HermitianLatticesTheory.normAt (Pi.basisFun B.LL (Fin n)) X v x = Formalism.HermitianLatticesTheory.normAt (Pi.basisFun B.LL (Fin n)) Xo v x
  simp only [Formalism.HermitianLatticesTheory.normAt, Formalism.HermitianLatticesTheory.fcoord, X, if_neg hv]

end GlobalTheory.Mem

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemKDSupUnitIdlIff
section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr
open GlobalTheory.Mem.Chr.IdlFact

namespace GlobalTheory.Mem.Chr.KDVal

variable {L : Type} [Field L] [NumberField L] (F : Type) [Field F] [NumberField F] [Algebra F L]

open Classical in

theorem valAt_locF (w : HeightOneSpectrum (𝓞 L)) (v : HeightOneSpectrum (𝓞 F)) (k : Fˣ) :
    valAt w (locF (L := L) F v k) =
      if w.under (𝓞 F) = v then WithZero.exp (-ordF w (upF F k)) else 1 := by
  unfold locF
  rw [map_prod]
  have hm : ∀ Q : HeightOneSpectrum (𝓞 L), Q ∈ aboveF (L := L) F v ↔ Q.under (𝓞 F) = v := fun Q => by
    simp [aboveF]
  split_ifs with hw
  · rw [Finset.prod_eq_single_of_mem w ((hm w).2 hw) (fun Q _ hQ => valAt_localIdele_ne hQ.symm _),
      valAt_localIdele_self]
    have h0 : w.valuation L ((upF F k : Lˣ) : L) ≠ 0 := by simp
    unfold ordF
    rw [neg_neg, WithZero.exp_log h0]
    exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w _
  · exact Finset.prod_eq_one fun Q hQ => valAt_localIdele_ne (fun e : w = Q => hw (by rw [e]; exact (hm Q).1 hQ)) _

def balanced : Subgroup (Ideles L) where
  carrier := {a | ∀ w w' : HeightOneSpectrum (𝓞 L), w'.under (𝓞 F) = w.under (𝓞 F) → valAt w a = valAt w' a}
  one_mem' := fun w w' _ => by rw [map_one, map_one]
  mul_mem' := fun {a b} ha hb w w' h => by rw [map_mul, map_mul, ha w w' h, hb w w' h]
  inv_mem' := fun {a} ha w w' h => by rw [map_inv, map_inv, ha w w' h]

theorem unitIdl_le_balanced : unitIdl L ≤ balanced (L := L) F := fun a ha w w' _ =>
  (ha w).trans (ha w').symm

variable {F}

theorem locF_mem_balanced
    (hu : ∀ (P : HeightOneSpectrum (𝓞 L)) (k : Fˣ), ordF P (upF F k) = ordF (P.under (𝓞 F)) k)
    (v : HeightOneSpectrum (𝓞 F)) (k : Fˣ) : locF (L := L) F v k ∈ balanced (L := L) F := fun w w' h => by
  rw [valAt_locF, valAt_locF, hu, hu, h]

theorem mem_sup_of_balanced
    (hu : ∀ (P : HeightOneSpectrum (𝓞 L)) (k : Fˣ), ordF P (upF F k) = ordF (P.under (𝓞 F)) k)
    (G : Subgroup (Ideles L)) (hG : ∀ v k, locF (L := L) F v k ∈ G) (a : Ideles L)
    (ha : a ∈ balanced (L := L) F) : a ∈ G ⊔ unitIdl L := by
  classical
  let T : Finset (HeightOneSpectrum (𝓞 F)) := (finite_valAt_ne_one a).toFinset.image fun w => w.under (𝓞 F)
  let m : HeightOneSpectrum (𝓞 F) → ℤ := fun v =>
    if h : ∃ w : HeightOneSpectrum (𝓞 L), w.under (𝓞 F) = v then -WithZero.log (valAt h.choose a) else 0
  let b : Ideles L := ∏ v ∈ T, locF (L := L) F v (unif v) ^ m v
  have hb : b ∈ G := prod_mem fun v _ => zpow_mem (hG _ _) _
  have hval : ∀ w, valAt w b = valAt w a := fun w => by
    have h1 : ∀ v, v ≠ w.under (𝓞 F) → valAt w (locF (L := L) F v (unif v) ^ m v) = 1 := fun v hv => by
      rw [map_zpow, valAt_locF, if_neg hv.symm, one_zpow]
    simp only [b]
    rw [map_prod]
    by_cases hw : w.under (𝓞 F) ∈ T
    · rw [Finset.prod_eq_single_of_mem _ hw (fun v _ hv => h1 v hv), map_zpow, valAt_locF, if_pos rfl, hu,
        ordF_unif_self, ← WithZero.exp_zsmul]
      have hex : ∃ w' : HeightOneSpectrum (𝓞 L), w'.under (𝓞 F) = w.under (𝓞 F) := ⟨w, rfl⟩
      have hm : m (w.under (𝓞 F)) = -WithZero.log (valAt w a) := by
        simp only [m]
        rw [dif_pos hex, ha w hex.choose hex.choose_spec]
      rw [hm]
      simp only [smul_eq_mul, mul_neg, neg_neg, mul_one]
      exact WithZero.exp_log (valAt_ne_zero w a)
    · rw [Finset.prod_eq_one (fun v hv => h1 v (fun e => hw (e ▸ hv)))]
      by_contra hne
      exact hw (Finset.mem_image_of_mem _ (by simpa using fun e => hne e.symm))
  have hu' : b⁻¹ * a ∈ unitIdl L := fun w => by
    rw [← valAt_apply, map_mul, map_inv, hval]
    exact inv_mul_cancel₀ (valAt_ne_zero w a)
  rw [← mul_inv_cancel_left b a]
  exact Subgroup.mul_mem_sup hb hu'

end GlobalTheory.Mem.Chr.KDVal

open GlobalTheory.Mem.Chr.KDVal in
open Classical in

theorem GlobalTheory.Mem.Chr.mem_KD_sup_unitIdl_iff : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (a : Ideles H.E), a ∈ KD H ⊔ unitIdl H.E ↔ ∀ w w', IsConjPl H w w' → Valued.v ((a : AdeleRing (𝓞 H.E) H.E).2 w) = Valued.v ((a : AdeleRing (𝓞 H.E) H.E).2 w') := by
  intro R H a
  obtain ⟨c, hc, hcm, hu, -⟩ := GlobalTheory.Mem.HostCM.host_cm R H
  have hiff : ∀ w w' : HeightOneSpectrum (𝓞 H.E),
      w'.under (𝓞 H.F) = w.under (𝓞 H.F) ↔ (w' = w ∨ IsConjPl H w w') := fun w w' => by
    rw [under_eq_iff_conjPl c hcm.rank hcm.ne, conjPl_main.2.1 R H w w']
    have : c.toRingEquiv = H.conj.toRingEquiv := RingEquiv.ext hc
    rw [this]
  constructor
  · intro ha w w' h
    have hle : KD H ⊔ unitIdl H.E ≤ balanced (L := H.E) H.F := by
      refine sup_le ((Subgroup.closure_le _).2 ?_) (unitIdl_le_balanced _)
      rintro x (hx | ⟨v, k, rfl⟩)
      · exact unitIdl_le_balanced _ hx.1
      · exact locF_mem_balanced hu v k
    exact hle ha w w' ((hiff w w').2 (Or.inr h))
  · intro h
    refine mem_sup_of_balanced hu _ (locF_mem_KD H) a fun w w' hw => ?_
    rcases (hiff w w').1 hw with rfl | h'
    · rfl
    · exact h w w' h'
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ModEqOneOfNorm
section
open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.Mem
open scoped TensorProduct

namespace GlobalTheory.Mem.LevelChoice

theorem mod_eq_one_of_norm {E : Type} [Field E] [NumberField E] (c : E →+* E) (π : 𝓞 E) (p m : ℕ) (hm : 1 < m)
    (hn : (π : E) * c (π : E) = (p : E)) (hc : π - 1 ∈ Ideal.span {((m : ℕ) : 𝓞 E)}) : p % m = 1 := by
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 hc
  have hπ : (π : E) = 1 + (a : E) * (m : E) := by
    have h := congrArg (fun x : 𝓞 E => (x : E)) ha
    simp only [map_mul, map_natCast, map_sub, map_one] at h
    change (a : E) * (m : E) = (π : E) - 1 at h
    rw [h]; ring
  have hai : IsIntegral ℤ (a : E) := a.2
  have hci : IsIntegral ℤ (c (a : E)) := hai.map c.toIntAlgHom
  have hmi : IsIntegral ℤ ((m : ℕ) : E) := by
    simpa using (isIntegral_algebraMap (R := ℤ) (A := E) (x := (m : ℤ)))
  have hm0 : (m : E) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  have hm0' : (m : ℚ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  have hx : algebraMap ℚ E (((p : ℚ) - 1) / m) = (a : E) + c a + (m : E) * ((a : E) * c a) := by
    rw [map_div₀, map_sub, map_natCast, map_natCast, map_one, ← hn, hπ, map_add, map_one, map_mul, map_natCast]
    field_simp
    ring
  have hxi : IsIntegral ℤ (algebraMap ℚ E (((p : ℚ) - 1) / m)) := by
    rw [hx]
    exact (hai.add hci).add (hmi.mul (hai.mul hci))
  have hqi : IsIntegral ℤ (((p : ℚ) - 1) / m) :=
    (isIntegral_algebraMap_iff (algebraMap ℚ E).injective).1 hxi
  obtain ⟨k, hk⟩ := IsIntegrallyClosed.isIntegral_iff.1 hqi
  have hk' : ((p : ℚ) - 1) = (k : ℚ) * m := by
    have : (k : ℚ) = ((p : ℚ) - 1) / m := by simpa using hk
    rw [this]; field_simp
  have hz : (p : ℤ) = 1 + (m : ℤ) * k := by
    have : ((p : ℤ) : ℚ) = ((1 + (m : ℤ) * k : ℤ) : ℚ) := by push_cast; linarith
    exact_mod_cast this
  have h1 : ((p % m : ℕ) : ℤ) = 1 := by
    rw [Int.natCast_mod, hz, Int.add_mul_emod_self_left]
    exact Int.emod_eq_of_lt (by norm_num) (by exact_mod_cast hm)
  exact_mod_cast h1

theorem exists_levCh : ∀ (P : PreCh) (du : P.Word → ℕ) (Ds Ga : ℝ), (∀ u, 0 < du u) → 0 < Ds → 1 < Ga → (∀ u, ∃ (π : 𝓞 P.H.E) (p : ℕ), p.Prime ∧ p ≠ P.H.pde ∧ p ≠ P.H.pde' ∧ (π : P.H.E) ∈ P.H.K ∧ (π : P.H.E) * P.H.conj (π : P.H.E) = (p : P.H.E) ∧ π - 1 ∈ Ideal.span {((P.H.QS * P.H.q * P.H.d * (P.H.g 0 * P.H.g 1) ^ 2 : ℕ) : 𝓞 P.H.E)} ∧ (Ds / du u) ^ ((1 : ℝ) / (P.R.f * P.R.k)) * Ga ^ (-(2 : ℝ) / (P.R.f * P.R.k)) ≤ (p : ℝ) ∧ (p : ℝ) ≤ (1 + 1 / ((P.R.f : ℝ) * P.R.k)) * ((Ds / du u) ^ ((1 : ℝ) / (P.R.f * P.R.k)) * Ga ^ (-(2 : ℝ) / (P.R.f * P.R.k)))) → ∃ L : LevCh P, L.duStar = du ∧ L.Dstar = Ds ∧ L.GamP = Ga := by
  intro P du Ds Ga hdu hDs hGa h
  choose π p hp h1 h2 hK hN hc hlo hhi using h
  have hq8 : P.H.q % 8 = 3 := P.H.hyp.2.2.1
  have hd16 : P.H.d % 16 = 7 := P.H.hyp.2.2.2.1
  have hn : 0 < P.H.QS := P.H.QS_pos
  have hm : 1 < P.H.QS * P.H.q * P.H.d := by
    have hq : 0 < P.H.q := by omega
    have hd : 0 < P.H.d := by omega
    have h1 : P.H.q ≤ P.H.QS * P.H.q := Nat.le_mul_of_pos_left _ hn
    have h2 : P.H.QS * P.H.q ≤ P.H.QS * P.H.q * P.H.d := Nat.le_mul_of_pos_right _ hd
    omega
  have hcond : ∀ u, p u % (P.H.QS * P.H.q * P.H.d) = 1 := fun u => by
    refine mod_eq_one_of_norm (P.H.conj : P.H.E →+* P.H.E) (π u) (p u) _ hm (hN u) ?_
    refine Ideal.span_singleton_le_span_singleton.2 ?_ (hc u)
    exact Nat.cast_dvd_cast (Dvd.intro _ rfl)
  exact ⟨{ T := p, T_prime := hp, T_cond := hcond, piT := π, piT_K := hK, piT_norm := hN, piT_cong := hc,
           T_ne_pde := fun u => ⟨h1 u, h2 u⟩, duStar := du, duStar_pos := hdu, Dstar := Ds, Dstar_pos := hDs,
           GamP := Ga, one_lt_gammaP := hGa, T_win := fun u => ⟨hlo u, hhi u⟩ }, rfl, rfl, rfl⟩

end GlobalTheory.Mem.LevelChoice
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistPowUnitsOfUnderEq
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr Classical

namespace GlobalTheory.Mem.Chr

theorem twist_pow_units_of_under_eq : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (S : Set ℕ) (ξ : HChar H.E), IsTwist H S ξ → ∀ (Q Q' : HeightOneSpectrum (𝓞 H.E)), Q.under (𝓞 H.F) = Q'.under (𝓞 H.F) → ∀ n : ℕ, (∀ x, IsUnitAt Q' x → ξ.loc Q' x ^ n = 1) → ∀ x, IsUnitAt Q x → ξ.loc Q x ^ n = 1 := by
  intro R H S ξ hξ Q Q' hu n hn x hx
  by_cases hQ : Q = Q'
  · subst hQ
    exact hn x hx
  by_cases hur : ξ.UnrAt Q
  · rw [hur x hx, one_pow]
  obtain ⟨-, htriv, htame, hram⟩ := hξ
  obtain ⟨-, hq, -, -⟩ := hram Q hur
  obtain ⟨a, k, hcop, hk, hcong⟩ := (GlobalTheory.localUnit_congr_global H.E Q x hx).2 _ hq rfl
  obtain ⟨c, -, hcm, -⟩ := GlobalTheory.Mem.HostCM.host_cm R H
  have hqQ : ((Ideal.absNorm Q.asIdeal : ℕ) : 𝓞 H.E) ∈ Q.asIdeal := Ideal.absNorm_mem Q.asIdeal
  have hqQ' : ((Ideal.absNorm Q.asIdeal : ℕ) : 𝓞 H.E) ∈ Q'.asIdeal := by
    have h1 : ((Ideal.absNorm Q.asIdeal : ℕ) : 𝓞 H.F) ∈ (Q.under (𝓞 H.F)).asIdeal := by
      show algebraMap (𝓞 H.F) (𝓞 H.E) _ ∈ Q.asIdeal
      rw [map_natCast]
      exact hqQ
    rw [hu] at h1
    have h2 : algebraMap (𝓞 H.F) (𝓞 H.E) ((Ideal.absNorm Q.asIdeal : ℕ) : 𝓞 H.F) ∈ Q'.asIdeal := h1
    rwa [map_natCast] at h2
  have hkQ : IsUnitAt Q (atFin Q k) := isUnitAt_nat (H := H) hqQ hcop hk
  have hkQ' : IsUnitAt Q' (atFin Q' k) := isUnitAt_nat (H := H) hqQ' hcop hk
  have hxk : IsUnitAt Q (x * (atFin Q k)⁻¹) := by
    unfold IsUnitAt at hx hkQ ⊢
    rw [Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀, hx, hkQ, inv_one, one_mul]
  have h1 : ξ.loc Q (x * (atFin Q k)⁻¹) = 1 := htame Q _ hxk (by simpa using hcong)
  rw [map_mul, map_inv, mul_inv_eq_one] at h1
  have ha0 : (a : H.F) ≠ 0 := by
    intro h
    have h0 : a = 0 := by exact_mod_cast h
    apply k.ne_zero
    rw [hk, h0, Nat.cast_zero]
  have hup : upF H.F (Units.mk0 (a : H.F) ha0) = k := by
    apply Units.ext
    rw [hk]
    exact map_natCast (algebraMap H.F H.E) a
  have hab : aboveF (L := H.E) H.F (Q.under (𝓞 H.F)) = {Q, Q'} := by
    have hc' : ConjPl c.toRingEquiv Q Q' :=
      ((under_eq_iff_conjPl c hcm.rank hcm.ne Q Q').1 hu.symm).resolve_left (Ne.symm hQ)
    ext P
    have hm : P ∈ aboveF (L := H.E) H.F (Q.under (𝓞 H.F)) ↔ P.under (𝓞 H.F) = Q.under (𝓞 H.F) := by
      unfold aboveF
      rw [Set.Finite.mem_toFinset]
      rfl
    rw [hm, under_eq_iff_conjPl c hcm.rank hcm.ne Q P, Finset.mem_insert, Finset.mem_singleton]
    refine or_congr Iff.rfl ⟨fun h => (existsUnique_conjPl _ Q).unique h hc', ?_⟩
    rintro rfl
    exact hc'
  have h2 := htriv.1 (Q.under (𝓞 H.F)) (Units.mk0 (a : H.F) ha0)
  rw [HChar.resFin_apply, hab, Finset.prod_pair hQ, hup] at h2
  have h3 : ξ.loc Q (atFin Q k) * ξ.loc Q' (atFin Q' k) = 1 := h2
  have h4 := congrArg (· ^ n) h3
  simp only [mul_pow, hn _ hkQ', mul_one, one_pow] at h4
  rw [h1, h4]

end GlobalTheory.Mem.Chr
end

