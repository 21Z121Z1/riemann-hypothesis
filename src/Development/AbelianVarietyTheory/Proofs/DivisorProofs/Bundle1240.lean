import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1200
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1177
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0046
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDominantOfSection
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1178
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1202
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1139

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemOpenNhdOneOfIntegralEqOneOnFinset
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open Topology

namespace GlobalTheory.FixLevOpen

variable {E : Type} [Field E] [NumberField E]

theorem isOpen_intAt (v : HeightOneSpectrum (𝓞 E)) :
    IsOpen (v.adicCompletionIntegers E : Set (v.adicCompletion E)) := by
  have h : (v.adicCompletionIntegers E : Set (v.adicCompletion E)) =
      ((Valued.v : Valuation (v.adicCompletion E) _).integer : Set (v.adicCompletion E)) := by
    ext x
    simp only [SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers, Valuation.mem_integer_iff]
  rw [h]
  exact Valued.isOpen_integer _

theorem tendsto_af {α : Type} {l : Filter α} (g : α → Af E) (c : Af E)
    (hc : ∀ v : HeightOneSpectrum (𝓞 E), pLoc E v c ∈ v.adicCompletionIntegers E)
    (h2 : ∀ᶠ a in l, ∀ v : HeightOneSpectrum (𝓞 E), pLoc E v (g a) ∈ v.adicCompletionIntegers E)
    (h3 : ∀ v : HeightOneSpectrum (𝓞 E), ∀ᶠ a in l, pLoc E v (g a) = pLoc E v c) :
    Tendsto g l (𝓝 c) := by
  let c' : Π v : HeightOneSpectrum (𝓞 E), v.adicCompletionIntegers E := fun v => ⟨pLoc E v c, hc v⟩
  have hcc : RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 E) => v.adicCompletion E)
      (fun v => (v.adicCompletionIntegers E : Set (v.adicCompletion E))) cofinite c' = c := by
    apply RestrictedProduct.ext
    intro v
    rfl
  let g' : α → Π v : HeightOneSpectrum (𝓞 E), v.adicCompletionIntegers E := fun a =>
    if h : ∀ v : HeightOneSpectrum (𝓞 E), pLoc E v (g a) ∈ v.adicCompletionIntegers E then fun v => ⟨pLoc E v (g a), h v⟩
    else c'
  have hg' : Tendsto g' l (𝓝 c') := by
    rw [tendsto_pi_nhds]
    intro v
    apply tendsto_const_nhds.congr'
    filter_upwards [h2, h3 v] with a ha hav
    simp only [g', dif_pos ha]
    exact Subtype.ext hav.symm
  have hmap := (tendsto_map (f := RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 E) => v.adicCompletion E)
      (fun v => (v.adicCompletionIntegers E : Set (v.adicCompletion E))) cofinite)).comp hg'
  rw [← RestrictedProduct.nhds_eq_map_structureMap (fun v => isOpen_intAt v), hcc] at hmap
  apply hmap.congr'
  filter_upwards [h2] with a ha
  simp only [Function.comp_apply, g', dif_pos ha]
  apply RestrictedProduct.ext
  intro v
  rfl

theorem tendsto_ad {α : Type} {l : Filter α} (g : α → Ad E) (c : Ad E)
    (hc : ∀ v : HeightOneSpectrum (𝓞 E), pLoc E v (pFin E c) ∈ v.adicCompletionIntegers E)
    (h1 : ∀ᶠ a in l, (g a).1 = c.1)
    (h2 : ∀ᶠ a in l, ∀ v : HeightOneSpectrum (𝓞 E), pLoc E v (pFin E (g a)) ∈ v.adicCompletionIntegers E)
    (h3 : ∀ v : HeightOneSpectrum (𝓞 E), ∀ᶠ a in l, pLoc E v (pFin E (g a)) = pLoc E v (pFin E c)) :
    Tendsto g l (𝓝 c) := by
  have hA : Tendsto (fun a => (g a).1) l (𝓝 c.1) := tendsto_const_nhds.congr' (h1.mono fun a ha => ha.symm)
  have hB : Tendsto (fun a => (g a).2) l (𝓝 c.2) := tendsto_af (fun a => (g a).2) c.2 hc h2 h3
  exact hA.prodMk_nhds hB

end GlobalTheory.FixLevOpen

namespace GlobalTheory.FixLevOpen

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem tendsto_mat {α : Type} {l : Filter α} (f : α → Matrix (Fin n) (Fin n) (Ad E))
    (h1 : ∀ᶠ a in l, ∀ i j, (f a i j).1 = ((1 : Matrix (Fin n) (Fin n) (Ad E)) i j).1)
    (h2 : ∀ᶠ a in l, ∀ (v : HeightOneSpectrum (𝓞 E)) i j, pLoc E v (pFin E (f a i j)) ∈ v.adicCompletionIntegers E)
    (h3 : ∀ v : HeightOneSpectrum (𝓞 E), ∀ᶠ a in l, ∀ i j,
      pLoc E v (pFin E (f a i j)) = pLoc E v (pFin E ((1 : Matrix (Fin n) (Fin n) (Ad E)) i j))) :
    Tendsto f l (𝓝 1) := by
  refine tendsto_pi_nhds.mpr fun i => tendsto_pi_nhds.mpr fun j => ?_
  apply tendsto_ad
  · intro v
    rcases eq_or_ne i j with rfl | h
    · rw [Matrix.one_apply_eq, map_one, map_one]
      exact one_mem _
    · rw [Matrix.one_apply_ne h, map_zero, map_zero]
      exact zero_mem _
  · exact h1.mono fun a ha => ha i j
  · exact h2.mono fun a ha v => ha v i j
  · exact fun v => (h3 v).mono fun a ha => ha i j

theorem inf_entry (u : finU E n) (i j : Fin n) :
    ((((u : UA E n) : GA E n) : Matrix (Fin n) (Fin n) (Ad E)) i j).1 = ((1 : Matrix (Fin n) (Fin n) (Ad E)) i j).1 := by
  have hu : cInf (u : UA E n) = 1 := u.2
  have h := congrArg (fun g : GL (Fin n) (Cinf E) => (g : Matrix (Fin n) (Fin n) (Cinf E)) i j) hu
  have h' : pInf E ((((u : UA E n) : GA E n) : Matrix (Fin n) (Fin n) (Ad E)) i j) =
      pInf E ((1 : Matrix (Fin n) (Fin n) (Ad E)) i j) := by
    refine h.trans ?_
    rcases eq_or_ne i j with rfl | hij
    · simp [Matrix.one_apply_eq]
    · simp [Matrix.one_apply_ne hij]
  have h'' : (infEq E).symm ((((u : UA E n) : GA E n) : Matrix (Fin n) (Fin n) (Ad E)) i j).1 =
      (infEq E).symm ((1 : Matrix (Fin n) (Fin n) (Ad E)) i j).1 := h'
  exact (infEq E).symm.injective h''

theorem mem_of_isOpen_of_eq_one_on_finset : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (U : Set (finU E n)), IsOpen U →
    (1 : finU E n) ∈ U → ∃ T : Finset (Pl E), ∀ u : finU E n, (∀ v ∈ T, cLoc v (u : UA E n) = 1) →
    (∀ (v : Pl E) (i j : Fin n), (cLoc v (u : UA E n)) i j ∈ v.adicCompletionIntegers E) →
    (∀ (v : Pl E) (i j : Fin n), (cLoc v (u : UA E n))⁻¹ i j ∈ v.adicCompletionIntegers E) → u ∈ U := by
  intro E _ _ _ n U hU h1
  let S : Finset (Pl E) → Set (finU E n) := fun T => {u | (∀ v ∈ T, cLoc v (u : UA E n) = 1) ∧
    (∀ (v : Pl E) (i j : Fin n), (cLoc v (u : UA E n)) i j ∈ v.adicCompletionIntegers E) ∧
    (∀ (v : Pl E) (i j : Fin n), (cLoc v (u : UA E n))⁻¹ i j ∈ v.adicCompletionIntegers E)}
  have hanti : ∀ T₁ T₂ : Finset (Pl E), T₁ ⊆ T₂ → S T₂ ⊆ S T₁ := fun T₁ T₂ h u hu =>
    ⟨fun v hv => hu.1 v (h hv), hu.2.1, hu.2.2⟩
  have hdir : Directed (fun x1 x2 => x1 ≥ x2) (fun T => 𝓟 (S T)) := by
    intro T₁ T₂
    refine ⟨T₁ ∪ T₂, ?_, ?_⟩
    · exact principal_mono.mpr (hanti _ _ Finset.subset_union_left)
    · exact principal_mono.mpr (hanti _ _ Finset.subset_union_right)
  let l : Filter (finU E n) := ⨅ T, 𝓟 (S T)
  have hmem : ∀ T, S T ∈ l := fun T => mem_iInf_of_mem T (mem_principal_self _)
  let ι : finU E n → GA E n := fun u => ((u : UA E n) : GA E n)
  have hι : Topology.IsInducing ι := Topology.IsInducing.subtypeVal.comp Topology.IsInducing.subtypeVal
  have hl : Tendsto id l (𝓝 (1 : finU E n)) := by
    rw [hι.tendsto_nhds_iff, Units.isEmbedding_embedProduct.isInducing.tendsto_nhds_iff]
    show Tendsto (fun u => (((ι u : GA E n) : Matrix (Fin n) (Fin n) (Ad E)),
      MulOpposite.op (((ι u)⁻¹ : GA E n) : Matrix (Fin n) (Fin n) (Ad E)))) l
      (𝓝 ((1 : Matrix (Fin n) (Fin n) (Ad E)), MulOpposite.op (1 : Matrix (Fin n) (Fin n) (Ad E))))
    refine Tendsto.prodMk_nhds ?_ (MulOpposite.continuous_op.tendsto _ |>.comp ?_)
    · apply tendsto_mat
      · exact Eventually.of_forall fun u i j => inf_entry u i j
      · filter_upwards [hmem ∅] with u hu
        exact fun v i j => hu.2.1 v i j
      · intro v
        filter_upwards [hmem {v}] with u hu
        intro i j
        have e1 := congrArg (fun g : GL (Fin n) (v.adicCompletion E) => g.val i j)
          (hu.1 v (Finset.mem_singleton_self v))
        have e2 := congrArg (fun g : GL (Fin n) (v.adicCompletion E) => g.val i j)
          (map_one (cLoc (E := E) (n := n) v))
        exact e1.trans e2.symm
    · apply tendsto_mat
      · exact Eventually.of_forall fun u i j => inf_entry u⁻¹ i j
      · filter_upwards [hmem ∅] with u hu
        intro v i j
        have := hu.2.2 v i j
        rwa [← map_inv] at this
      · intro v
        filter_upwards [hmem {v}] with u hu
        intro i j
        have hv : cLoc v ((u : UA E n)⁻¹) = 1 := by
          rw [map_inv, hu.1 v (Finset.mem_singleton_self v), inv_one]
        have e1 := congrArg (fun g : GL (Fin n) (v.adicCompletion E) => g.val i j) hv
        have e2 := congrArg (fun g : GL (Fin n) (v.adicCompletion E) => g.val i j)
          (map_one (cLoc (E := E) (n := n) v))
        exact e1.trans e2.symm
  have hU' : U ∈ l := hl (hU.mem_nhds h1)
  rw [mem_iInf_of_directed hdir] at hU'
  obtain ⟨T, hT⟩ := hU'
  exact ⟨T, fun u a b c => mem_principal.mp hT ⟨a, b, c⟩⟩

end GlobalTheory.FixLevOpen
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulHomInjective
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.TwOrbLat

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {w : Pl E} {K : GlobalTheory.UnitLemma.UQ}
  (e : K.E ≃+* w.adicCompletion E) {a : ℕ} {B : GlobalTheory.UnitLemma.InvAlg K} (b : Module.Basis (Fin a) K.E B.A)

def crd (y : B.A) : Fin a → w.adicCompletion E := fun i => e (b.repr y i)

def ofCrd (v : Fin a → w.adicCompletion E) : B.A := b.equivFun.symm fun i => e.symm (v i)

def mulHom : B.A →+* Matrix (Fin a) (Fin a) (w.adicCompletion E) :=
  e.toRingHom.mapMatrix.comp (Algebra.leftMulMatrix b).toRingHom

def mulGL : B.Aˣ →* GLw a w := Units.map (mulHom e b).toMonoidHom

theorem mulHom_eq (t : B.A) : mulHom e b t = GlobalTheory.TwLat.mulMat e b t := by
  ext i j
  simp [mulHom, GlobalTheory.TwLat.mulMat, Algebra.leftMulMatrix_apply]

theorem latOf_eq (q : GLw a w) :
    GlobalTheory.TwLat.lat e b q = Submodule.span K.O (Set.range fun j => ofCrd e b fun i => q.val i j) := by
  simp [GlobalTheory.TwLat.lat, ofCrd, Module.Basis.equivFun_symm_apply]

theorem crd_ofCrd (v : Fin a → w.adicCompletion E) : crd e b (ofCrd e b v) = v := by
  funext i
  simp only [crd, ofCrd]
  rw [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]

theorem ofCrd_crd (y : B.A) : ofCrd e b (crd e b y) = y := by
  simp [crd, ofCrd]

theorem mulHom_apply (t : B.A) (i j : Fin a) : mulHom e b t i j = e (b.repr (t * b j) i) := by
  simp [mulHom, Algebra.leftMulMatrix_eq_repr_mul]

theorem mulGL_val (t : B.Aˣ) : (mulGL e b t).val = GlobalTheory.TwLat.mulMat e b t := mulHom_eq e b t

theorem mulHom_injective : Function.Injective (mulHom e b) := by
  intro x y h
  apply Algebra.leftMulMatrix_injective b
  ext i j
  have := congrFun (congrFun h i) j
  exact e.injective (by simpa [mulHom] using this)

theorem mulGL_injective : Function.Injective (mulGL e b) := by
  intro x y h
  exact Units.ext (mulHom_injective e b (congrArg Units.val h))

theorem crd_injective : Function.Injective (crd e b) := fun x y h => by
  rw [← ofCrd_crd e b x, h, ofCrd_crd]

theorem crd_add (y z : B.A) : crd e b (y + z) = crd e b y + crd e b z := by
  funext i; simp [crd]

theorem crd_smul (c : K.E) (y : B.A) : crd e b (c • y) = e c • crd e b y := by
  funext i; simp [crd]

theorem crd_mul (t y : B.A) : crd e b (t * y) = mulHom e b t *ᵥ crd e b y := by
  funext i
  simp only [crd, mulHom, RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  rw [← Algebra.leftMulMatrix_mulVec_repr]
  simp [Matrix.mulVec, dotProduct, RingHom.mapMatrix_apply, crd]

theorem ofCrd_mulVec (t : B.A) (v : Fin a → w.adicCompletion E) :
    ofCrd e b (mulHom e b t *ᵥ v) = t * ofCrd e b v := by
  apply crd_injective e b
  rw [crd_mul, crd_ofCrd, crd_ofCrd]

theorem col_mul (M N : Matrix (Fin a) (Fin a) (w.adicCompletion E)) (j : Fin a) :
    (fun i => (M * N) i j) = M *ᵥ fun i => N i j := by
  funext i; simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]

theorem crd_sum (s : Finset (Fin a)) (f : Fin a → B.A) : crd e b (∑ j ∈ s, f j) = ∑ j ∈ s, crd e b (f j) := by
  induction s using Finset.induction_on with
  | empty => funext i; simp [crd]
  | insert j s hj ih => rw [Finset.sum_insert hj, Finset.sum_insert hj, crd_add, ih]

theorem latOf_mul (t : B.Aˣ) (q : GLw a w) :
    GlobalTheory.TwLat.lat e b (mulGL e b t * q) = GlobalTheory.UnitLemma.mulLat K.O (t : B.A) (GlobalTheory.TwLat.lat e b q) := by
  rw [latOf_eq, latOf_eq]
  unfold GlobalTheory.UnitLemma.mulLat
  rw [Submodule.map_span, ← Set.range_comp]
  refine congrArg (Submodule.span K.O) (congrArg Set.range (funext fun j => ?_))
  simp only [Function.comp_apply, LinearMap.mulLeft_apply, Units.val_mul]
  change (ofCrd e b fun i => (mulHom e b (t : B.A) * q.val) i j) = _
  rw [col_mul (mulHom e b (t : B.A)) q.val j, ofCrd_mulVec]

theorem latOf_isLat (q : GLw a w) : GlobalTheory.UnitLemma.IsLat K.O K.E (GlobalTheory.TwLat.lat e b q) := by
  refine ⟨Submodule.fg_span (Set.finite_range _), ?_⟩
  rw [latOf_eq, Submodule.span_span_of_tower, eq_top_iff]
  intro z _
  rw [Submodule.mem_span_range_iff_exists_fun]
  refine ⟨fun j => e.symm (((q⁻¹ : GLw a w).val *ᵥ crd e b z) j), ?_⟩
  apply crd_injective e b
  rw [crd_sum]
  have h1 : crd e b z = q.val *ᵥ ((q⁻¹ : GLw a w).val *ᵥ crd e b z) := by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  conv_rhs => rw [h1]
  funext i
  simp [crd_smul, crd_ofCrd, Finset.sum_apply, Matrix.mulVec, dotProduct, mul_comm]

end GlobalTheory.TwOrbLat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegInvRatioIsNormOfNegRatioIsNorm
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published GlobalTheory.QSA GlobalTheory.PlaneSU
open scoped TensorProduct Quaternion

namespace GlobalTheory.PlaneSU.NormSwap

theorem neg_inv_ratio_norm : ∀ (F E : Type) [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) (δ : F) (b : Module.Basis (Fin 2) F E), b 0 = 1 → σ (b 1) = -b 1 → b 1 * b 1 = algebraMap F E δ → ∀ f₁ f₂ : F, f₁ ≠ 0 → f₂ ≠ 0 → ∀ (R : Type) [CommRing R] [Algebra F R] (ε : R) (t : R ⊗[F] E), algebraMap R (R ⊗[F] E) ε * (t * sigR R σ t + algebraMap F (R ⊗[F] E) (f₁ / f₂)) = 0 → ∃ p q : R, ε * (algebraMap F R (-(f₂ / f₁)) - (p ^ 2 - algebraMap F R δ * q ^ 2)) = 0 := by
  intro F E _ _ _ σ δ b hb0 hb1 hsq f₁ f₂ hf₁ hf₂ R _ _ ε t hε
  let B := Algebra.TensorProduct.basis R b
  have hB : ∀ i, B i = 1 ⊗ₜ[F] b i := fun i => Algebra.TensorProduct.basis_apply b i
  have h0 : B 0 = 1 := by rw [hB, hb0]; rfl
  have h1 : B 1 * B 1 = algebraMap F R δ • B 0 := by
    rw [hB, hB, Algebra.TensorProduct.tmul_mul_tmul, hsq, hb0, Algebra.algebraMap_eq_smul_one (A := E),
      TensorProduct.tmul_smul, one_mul, algebraMap_smul]
  have hs : ∀ (r : R) (e : E), sigR R σ (r ⊗ₜ[F] e) = r ⊗ₜ[F] σ e := fun r e => rfl
  have key : ∀ x y : R, (x • B 0 + y • B 1) * sigR R σ (x • B 0 + y • B 1) =
      algebraMap R (R ⊗[F] E) (x ^ 2 - algebraMap F R δ * y ^ 2) := by
    intro x y
    have e : sigR R σ (x • B 0 + y • B 1) = x • B 0 - y • B 1 := by
      rw [map_add, hB, hB, TensorProduct.smul_tmul', TensorProduct.smul_tmul', hs, hs, hb1, hb0,
        map_one, TensorProduct.tmul_neg, sub_eq_add_neg]
    rw [e]
    rw [h0] at h1 ⊢
    generalize algebraMap F R δ = d at h1 ⊢
    simp only [Algebra.smul_def, mul_one, map_sub, map_mul, map_pow] at h1 ⊢
    linear_combination (-(algebraMap R (R ⊗[F] E) y) ^ 2) * h1
  have hz := B.sum_repr t
  rw [Fin.sum_univ_two] at hz
  set p₀ := B.repr t 0
  set q₀ := B.repr t 1
  rw [← hz, key, IsScalarTower.algebraMap_apply F R (R ⊗[F] E), ← map_add, ← map_mul] at hε
  have hinj : Function.Injective (algebraMap R (R ⊗[F] E)) := by
    have := Algebra.TensorProduct.includeLeft_injective (R := F) (S := F) (A := R) (B := E)
      (algebraMap F E).injective
    intro x y hxy
    apply this
    simpa [Algebra.TensorProduct.algebraMap_apply] using hxy
  have h : ε * (p₀ ^ 2 - algebraMap F R δ * q₀ ^ 2 + algebraMap F R (f₁ / f₂)) = 0 :=
    hinj (by rw [hε, map_zero])
  set c := algebraMap F R (f₂ / f₁)
  have hca : c * algebraMap F R (f₁ / f₂) = 1 := by
    rw [← map_mul, div_mul_div_comm, mul_comm f₂ f₁, div_self (mul_ne_zero hf₁ hf₂), map_one]
  refine ⟨c * p₀, c * q₀, ?_⟩
  rw [map_neg]
  linear_combination (-c ^ 2) * h + ε * c * hca

end GlobalTheory.PlaneSU.NormSwap
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormPolarisedTopChernCoeffLeOfWeightedBound
section
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop

theorem norm_mixTop_le_of_weighted : ∀ {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (K : Fin n → EndValuedForm11Coeffs n r) (w : Fin n → ℝ) (c : ℝ), (∀ a, 0 < w a) → (∀ i a b p q, ‖K i a b p q‖ * (w a * w b) ≤ c) → ‖mixTop K‖ ≤ (Fintype.card r : ℝ) ^ n * (n.factorial : ℝ) ^ 2 * |c| ^ n * ∏ a, (w a)⁻¹ ^ 2 := by
  intro n r _ _ K w c hw hK
  set D : ℝ := (n.factorial : ℝ) * |c| ^ n * ∏ a, (w a)⁻¹ ^ 2 with hD
  have hs : ∀ σ : Equiv.Perm (Fin n), ‖((Equiv.Perm.sign σ : ℤ) : ℂ)‖ = 1 := by
    intro σ
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
  have hterm : ∀ (p : Fin n → r) (π u : Equiv.Perm (Fin n)),
      ‖((Equiv.Perm.sign π : ℤ) : ℂ) * ((Equiv.Perm.sign u : ℤ) : ℂ) *
        (Matrix.of fun i b => K i (u i) b (p i) (p (π i))).det‖ ≤ D := by
    intro p π u
    rw [norm_mul, norm_mul, hs, hs, one_mul, one_mul]
    exact GlobalTheory.T.norm_det_le_of_weighted_entry_bound _ u w c hw (fun i b => by simpa using hK i (u i) b (p i) (p (π i)))
  have hsum : ‖∑ p : Fin n → r, ∑ π : Equiv.Perm (Fin n), ∑ u : Equiv.Perm (Fin n),
      ((Equiv.Perm.sign π : ℤ) : ℂ) * ((Equiv.Perm.sign u : ℤ) : ℂ) *
        (Matrix.of fun i b => K i (u i) b (p i) (p (π i))).det‖ ≤
      (Fintype.card r : ℝ) ^ n * ((n.factorial : ℝ) * ((n.factorial : ℝ) * D)) := by
    refine (norm_sum_le _ _).trans ?_
    refine (Finset.sum_le_sum fun p _ => (norm_sum_le _ _).trans
      (Finset.sum_le_sum fun π _ => (norm_sum_le _ _).trans
        (Finset.sum_le_sum fun u _ => hterm p π u))).trans ?_
    simp [Finset.sum_const, Fintype.card_perm, Fintype.card_fun]
  have hf : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  unfold mixTop
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  calc (n.factorial : ℝ)⁻¹ * ‖_‖ ≤ (n.factorial : ℝ)⁻¹ *
        ((Fintype.card r : ℝ) ^ n * ((n.factorial : ℝ) * ((n.factorial : ℝ) * D))) :=
        mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hf.le)
    _ = _ := by rw [hD]; field_simp

end GlobalTheory.GoodTop
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormRootOfUnitary
section
namespace GlobalTheory.UnitaryCharpolyRootNorm

open Matrix NumberField

theorem norm_root_of_unitary {m : Type} [Fintype m] [DecidableEq m] (A : Matrix m m ℂ) (hA : Aᴴ * A = 1) (z : ℂ)
    (hz : A.charpoly.IsRoot z) : ‖z‖ = 1 := by
  have hdet : (Matrix.scalar m z - A).det = 0 := by
    rw [← Matrix.eval_charpoly]; exact hz
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have hAv : A *ᵥ v = z • v := by
    rw [Matrix.sub_mulVec, sub_eq_zero] at hv
    rw [← hv]
    ext i
    simp [Matrix.mulVec_diagonal]
  have h1 : star (A *ᵥ v) ⬝ᵥ (A *ᵥ v) = star v ⬝ᵥ v := by
    rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, hA, Matrix.one_mulVec]
  rw [hAv, star_smul, smul_dotProduct, dotProduct_smul, smul_smul] at h1
  have hne : star v ⬝ᵥ v ≠ 0 := by
    open scoped ComplexOrder in
    exact fun h => hv0 (dotProduct_star_self_eq_zero.mp h)
  have h2 : star z * z = 1 := by
    apply mul_right_cancel₀ hne
    rw [one_mul]; exact h1
  have h3 : ‖z‖ * ‖z‖ = 1 := by
    have := congrArg norm h2
    rwa [norm_mul, norm_star, norm_one] at this
  nlinarith [norm_nonneg z]

theorem norm_root_charpoly {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (γ : GlobalTheory.BCT.UE E n)
    (τ : E →+* ℂ) :
    ∀ z ∈ (Polynomial.map τ (Matrix.charpoly ((γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E))).roots,
      ‖z‖ = (1 : ℝ) := by
  intro z hz
  set g : Matrix (Fin n) (Fin n) E := ((γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) with hg
  have h : (Matrix.of fun i j => IsCMField.complexConj E (g j i)) * 1 * g = 1 := γ.2
  rw [mul_one] at h
  have hA : (g.map τ)ᴴ * g.map τ = 1 := by
    have e : (g.map τ)ᴴ = (Matrix.of fun i j => IsCMField.complexConj E (g j i)).map τ := by
      ext i j
      simp [IsCMField.complexEmbedding_complexConj]
    rw [e, ← Matrix.map_mul, h, Matrix.map_one _ (map_zero τ) (map_one τ)]
  apply norm_root_of_unitary _ hA
  rw [Matrix.charpoly_map]
  exact Polynomial.isRoot_of_mem_roots hz

end GlobalTheory.UnitaryCharpolyRootNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NotIsUnitOffDiagonalTransitionOnCommonSection
section
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

namespace GlobalTheory.FlagPush.OnSection

theorem not_unitAt_of_eq {F : Type} [Field F] {X Y : Var F} {ι : Type} {m : ι → ℕ} {E : Fr (ratOf X) m 0}
    {E' : Fr (ratOf Y) m m} {φ : X.Fn →ₐ[F] Y.Fn} {f : Y.X ⟶ X.X} (hf : Refines E E' φ f) (W : Dbl Y)
    (hα : ∀ u : X.Fn, W.α₁ (φ u) = W.α₂ (φ u)) (τ : ι) (a b : Fin (m τ)) (hab : a ≠ b) {k : Type} [Field k]
    (w : Sp k ⟶ W.Z) (hw : w ≫ W.p₁ = w ≫ W.p₂) (A : Mat m Y.Fn)
    (hA : A ∈ E'.S (W.p₁ (w (IsLocalRing.closedPoint k)))) :
    ¬ UnitAt (w (IsLocalRing.closedPoint k)) ((A.map W.α₁ * (A.map W.α₂)⁻¹) τ a b) := by
  obtain ⟨ev, hev, hq⟩ := GlobalTheory.T.exists_eval_regular_functions_at_fieldPoint F Y W.Z k w
  have hp : W.p₂ (w (IsLocalRing.closedPoint k)) = W.p₁ (w (IsLocalRing.closedPoint k)) :=
    (Scheme.Hom.comp_apply _ _ _).symm.trans
      ((congrArg (fun q : Sp k ⟶ Y.X => q (IsLocalRing.closedPoint k)) hw.symm).trans (Scheme.Hom.comp_apply _ _ _))
  obtain ⟨A₀, hA₀⟩ := E.nonempty (f (W.p₁ (w (IsLocalRing.closedPoint k))))
  have hM := hf.sub _ A hA A₀ hA₀
  have hd : ∀ σ, (A₀.map φ σ).det ≠ 0 := fun σ => by
    have := Mat.det_map A₀ (φ : X.Fn →+* Y.Fn) σ
    exact this.trans_ne ((map_ne_zero _).2 (Fr.det_ne hA₀ σ))
  generalize hB : A₀.map φ = B at hM hd
  have hB12 : B.map W.α₁ = B.map W.α₂ := by
    subst hB
    funext σ
    ext i j
    exact hα _
  have h1 : ∀ u ∈ ((ratOf Y).O (W.p₁ (w (IsLocalRing.closedPoint k)))).toSubring,
      ∃ h, ev ⟨W.α₁ u, h⟩ = (ratOf Y).val (w ≫ W.p₁) u := fun u hu => hq W.p₁ u (mem_O_ratOf.1 hu)
  have h2 : ∀ u ∈ ((ratOf Y).O (W.p₁ (w (IsLocalRing.closedPoint k)))).toSubring,
      ∃ h, ev ⟨W.α₂ u, h⟩ = (ratOf Y).val (w ≫ W.p₁) u := fun u hu => by
    obtain ⟨h, e⟩ := hq W.p₂ u (by rw [hp]; exact mem_O_ratOf.1 hu)
    exact ⟨h, e.trans (congrArg (fun q => (ratOf Y).val q u) hw.symm)⟩
  have hN₁ := hM.map W.α₁ fun u hu => (h1 u hu).choose
  have hN₂ := hM.map W.α₂ fun u hu => (h2 u hu).choose
  have hd₂ : ∀ σ, (B.map W.α₂ σ).det ≠ 0 := fun σ => (Mat.det_map B W.α₂ σ).trans_ne ((map_ne_zero _).2 (hd σ))
  have hg : A.map W.α₁ * (A.map W.α₂)⁻¹ = (A * B⁻¹).map W.α₁ * ((A * B⁻¹).map W.α₂)⁻¹ := by
    rw [Mat.map_mul, Mat.map_mul, Mat.map_inv, Mat.map_inv, hB12, Mat.mul_inv_rev, Mat.inv_inv hd₂, mul_assoc,
      ← mul_assoc _ (B.map W.α₂), Mat.inv_mul hd₂, one_mul]
  rw [hg]
  have hG := hN₁.mul hN₂.inv
  let v : W.Z.functionField → k := fun u => if h : u ∈ (algebraMap (W.Z.presheaf.stalk (w (IsLocalRing.closedPoint k)))
    W.Z.functionField).range then ev ⟨u, h⟩ else 0
  have hv : ∀ x : (algebraMap (W.Z.presheaf.stalk (w (IsLocalRing.closedPoint k))) W.Z.functionField).range,
      v (x : W.Z.functionField) = ev x := fun x => dif_pos x.2
  have e1 := Par.map_mul_of hG hN₂ v ev hv
  rw [mul_assoc, Mat.inv_mul hN₂.det_ne, mul_one] at e1
  have e2 : ((A * B⁻¹).map W.α₁).map v = ((A * B⁻¹).map W.α₂).map v := by
    funext σ
    ext i j
    obtain ⟨p, hp⟩ := h1 _ ((hM σ).1 i j)
    obtain ⟨q, hq⟩ := h2 _ ((hM σ).1 i j)
    exact ((hv ⟨_, p⟩).trans hp).trans ((hv ⟨_, q⟩).trans hq).symm
  have hV := (Par.map_of hN₂ v ev hv).det_ne
  have e3 : ((A * B⁻¹).map W.α₁ * ((A * B⁻¹).map W.α₂)⁻¹).map v = 1 := by
    have := congrArg (· * (((A * B⁻¹).map W.α₂).map v)⁻¹) (e1.symm.trans e2)
    simpa only [mul_assoc, Mat.mul_inv hV, mul_one] using this
  intro hu
  refine (hev ⟨_, (hG τ).1 a b⟩).2 hu ((hv ⟨_, (hG τ).1 a b⟩).symm.trans ?_)
  exact (congrFun (congrFun (congrFun e3 τ) a) b).trans (Matrix.one_apply_ne hab)

end GlobalTheory.FlagPush.OnSection

theorem GlobalTheory.FlagPush.not_unitAt_section : ∀ (F : Type) [Field F] (X Y : Var F) (ι : Type) [Fintype ι] (m : ι → ℕ) (E : Fr (ratOf X) m 0) (E' : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X), Refines E E' φ f → ∀ W : Dbl Y, (∀ u : X.Fn, W.α₁ (φ u) = W.α₂ (φ u)) → ∀ (τ : ι) (a b : Fin (m τ)), a ≠ b → ∀ y : Y.X, ∀ A ∈ E'.S y, ¬ UnitAt (W.δ y) ((A.map W.α₁ * (A.map W.α₂)⁻¹) τ a b) := by
  intro F _ X Y ι _ m E E' φ f hf W hα τ a b hab y A hA
  let w₀ : Sp (Y.X.residueField y) ⟶ Y.X := Y.X.fromSpecResidueField y
  have h0 : w₀ (IsLocalRing.closedPoint _) = y := Scheme.fromSpecResidueField_apply _ _
  have h1 : (w₀ ≫ W.δ) (IsLocalRing.closedPoint _) = W.δ y := (Scheme.Hom.comp_apply _ _ _).trans (congrArg _ h0)
  have h2 : W.p₁ (W.δ y) = y := by rw [← Scheme.Hom.comp_apply, W.δ₁]; rfl
  have := OnSection.not_unitAt_of_eq hf W hα τ a b hab (w₀ ≫ W.δ)
    (by rw [Category.assoc, Category.assoc, W.δ₁, W.δ₂]) A (by rw [h1, h2]; exact hA)
  rwa [h1] at this
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisationOperatorFormulaGroupAndProjectorsStatement
section
open Formalism.CohomologicalDescent.DepthNonnegative GlobalTheory.ExpFrame Formalism.CohomologicalDescent.LD GlobalTheory.CapelliLink
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polarisationOperator_formula_groupAndProjectors : ∀ (O : Type) [CommRing O] (N : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (τ : ι) (M : ℕ) (a b : Fin N), ∃ F : FreeAlgebra O (Letter O N ι), ∀ (lam : ι → ℕ → ℕ) (P : ι → (Fin N → ℕ) → Module.End O (NablaT O N lam)), (∀ σ, Antitone (res N (lam σ))) → (∀ σ w, IsProj O N lam σ w (P σ w)) → ∑ c : Fin N, lam τ c ≤ M → ∀ x : ∀ σ, Formalism.GradedWeylDivisibility.dualWeyl O N N (res N (lam σ)), ∃ y : Formalism.GradedWeylDivisibility.dualWeyl O N N (res N (lam τ)), (y : MvPolynomial (Fin N × Fin N) O) = Formalism.GradedWeylDivisibility.rowDiv O a b 1 (x τ : MvPolynomial (Fin N × Fin N) O) ∧ evalE O N lam P F (PiTensorProduct.tprod O x) = PiTensorProduct.tprod O (Function.update x τ y) := by
  first | exact @GlobalTheory.PolarFormula.polar_formula | exact GlobalTheory.PolarFormula.polar_formula | (intros; apply GlobalTheory.PolarFormula.polar_formula <;> assumption)
end

