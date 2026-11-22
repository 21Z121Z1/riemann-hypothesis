import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0300
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0334
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0347
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0339
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0272
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0119
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0016
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0344
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0284
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StdLvPr
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0285
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsClassSumPairingFormsLat
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0337
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0307
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0297
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfInnerSmooth
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0079
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0176
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SideMultiplicityFamily

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NontrivialOfNeBot
section
noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU

namespace GlobalTheory.DefU.Pairs

section Abstract

variable {H S F P P' : Type} [Group H] [AddCommGroup S] [Module ℂ S] [AddCommGroup F] [Module ℂ F]
  [AddCommGroup P] [Module ℂ P] [AddCommGroup P'] [Module ℂ P']

def img (j : P →ₗ[ℂ] S →ₗ[ℂ] F) : Submodule ℂ F := Submodule.span ℂ {φ | ∃ p v, j p v = φ}

theorem apply_mem_img (j : P →ₗ[ℂ] S →ₗ[ℂ] F) (p : P) (v : S) : j p v ∈ img j :=
  Submodule.subset_span ⟨p, v, rfl⟩

variable {ι : Type} [Fintype ι]

def total (b : ι → S) (j : P →ₗ[ℂ] S →ₗ[ℂ] F) : (ι → P) →ₗ[ℂ] F :=
  ∑ a, (LinearMap.applyₗ (b a)) ∘ₗ j ∘ₗ LinearMap.proj a

theorem total_apply (b : ι → S) (j : P →ₗ[ℂ] S →ₗ[ℂ] F) (c : ι → P) :
    total b j c = ∑ a, j (c a) (b a) := by
  simp [total, LinearMap.sum_apply]

theorem total_repr (b : Module.Basis ι ℂ S) (j : P →ₗ[ℂ] S →ₗ[ℂ] F) (p : P) (v : S) :
    total b j (fun a => b.repr v a • p) = j p v := by
  rw [total_apply]
  conv_rhs => rw [← b.sum_repr v, map_sum]
  simp

theorem range_total (b : Module.Basis ι ℂ S) (j : P →ₗ[ℂ] S →ₗ[ℂ] F) :
    LinearMap.range (total b j) = img j := by
  refine le_antisymm ?_ (Submodule.span_le.2 ?_)
  · rintro _ ⟨c, rfl⟩
    rw [total_apply]
    exact Submodule.sum_mem _ fun a _ => apply_mem_img j _ _
  · rintro _ ⟨p, v, rfl⟩
    exact ⟨_, total_repr b j p v⟩

theorem coeff_mem {ρ : Representation ℂ H S} (hsp : Submodule.span ℂ (Set.range ρ) = ⊤) {R : H → Module.End ℂ F}
    {j : P →ₗ[ℂ] S →ₗ[ℂ] F} (hj : ∀ p x v, j p (ρ x v) = R x (j p v)) {U : Submodule ℂ F}
    (hU : ∀ x, ∀ u ∈ U, R x u ∈ U) (b : Module.Basis ι ℂ S) {c : ι → P} (h : total b j c ∈ U) (a : ι) (w : S) :
    j (c a) w ∈ U := by
  classical
  have key : ∀ T : Module.End ℂ S, ∑ a, j (c a) (T (b a)) ∈ U := fun T => by
    have hT : T ∈ Submodule.span ℂ (Set.range ρ) := hsp ▸ Submodule.mem_top
    induction hT using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, rfl⟩ := hx
      have e : ∑ a, j (c a) (ρ g (b a)) = R g (total b j c) := by
        rw [total_apply, map_sum]
        exact Finset.sum_congr rfl fun a _ => hj _ _ _
      rw [e]
      exact hU _ _ h
    | zero => simp
    | add x y _ _ hx hy => simpa [Finset.sum_add_distrib] using add_mem hx hy
    | smul r x _ hx => simpa [Finset.smul_sum] using U.smul_mem r hx
  have h1 := key ((b.coord a).smulRight w)
  rw [Finset.sum_eq_single a (fun a' _ h' => by simp [Module.Basis.coord_apply, Finsupp.single_apply, h'])
    (fun h' => absurd (Finset.mem_univ a) h')] at h1
  simpa [Module.Basis.coord_apply] using h1

theorem eq_bot_or_eq_img [FiniteDimensional ℂ S] {K : Type} {ρ : Representation ℂ H S}
    (hsp : Submodule.span ℂ (Set.range ρ) = ⊤) {R : H → Module.End ℂ F} {j : P →ₗ[ℂ] S →ₗ[ℂ] F}
    (hj : ∀ p x v, j p (ρ x v) = R x (j p v)) {Q : K → Module.End ℂ P}
    {T : K → Module.End ℂ F} (hQ : ∀ k p v, j (Q k p) v = T k (j p v))
    (hP : ∀ N : Submodule ℂ P, (∀ k, ∀ p ∈ N, Q k p ∈ N) → N = ⊥ ∨ N = ⊤) {U : Submodule ℂ F} (hle : U ≤ img j)
    (hU : ∀ x, ∀ u ∈ U, R x u ∈ U) (hT : ∀ k, ∀ u ∈ U, T k u ∈ U) : U = ⊥ ∨ U = img j := by
  let N : Submodule ℂ P := ⨅ v : S, U.comap ((LinearMap.applyₗ v) ∘ₗ j)
  have hN : ∀ p, p ∈ N ↔ ∀ v, j p v ∈ U := fun p => by simp [N, Submodule.mem_iInf]
  rcases hP N fun k p hp => (hN _).2 fun v => by
      rw [hQ]
      exact hT _ _ ((hN p).1 hp v) with h | h
  · left
    refine (Submodule.eq_bot_iff _).2 fun φ hφ => ?_
    let b := Module.finBasis ℂ S
    obtain ⟨c, rfl⟩ : φ ∈ LinearMap.range (total b j) := by
      rw [range_total]
      exact hle hφ
    have hc : ∀ a, c a = 0 := fun a => by
      have : c a ∈ N := (hN _).2 fun w => coeff_mem hsp hj hU b hφ a w
      rwa [h, Submodule.mem_bot] at this
    rw [total_apply]
    simp [hc]
  · right
    refine le_antisymm hle (Submodule.span_le.2 ?_)
    rintro _ ⟨p, v, rfl⟩
    exact (hN p).1 (h ▸ Submodule.mem_top) v

def part (Alg : Submodule ℂ (S →ₗ[ℂ] F)) (A : Submodule ℂ F) : Submodule ℂ Alg :=
  ⨅ v : S, A.comap ((LinearMap.applyₗ v).comp Alg.subtype)

theorem mem_part {Alg : Submodule ℂ (S →ₗ[ℂ] F)} {A : Submodule ℂ F} {f : Alg} : f ∈ part Alg A ↔ ∀ v, f.1 v ∈ A :=
  Submodule.mem_iInf _

def partVal (Alg : Submodule ℂ (S →ₗ[ℂ] F)) (A : Submodule ℂ F) : part Alg A →ₗ[ℂ] S →ₗ[ℂ] A where
  toFun f := f.1.1.codRestrict A (mem_part.1 f.2)
  map_add' _ _ := LinearMap.ext fun _ => Subtype.ext rfl
  map_smul' _ _ := LinearMap.ext fun _ => Subtype.ext rfl

def partMap {Alg : Submodule ℂ (S →ₗ[ℂ] F)} {A B : Submodule ℂ F} (t : A →ₗ[ℂ] B)
    (ht : ∀ f : part Alg A, B.subtype ∘ₗ t ∘ₗ partVal Alg A f ∈ Alg) : part Alg A →ₗ[ℂ] part Alg B :=
  LinearMap.codRestrict _ (LinearMap.codRestrict Alg
    ((LinearMap.llcomp ℂ S A F (B.subtype ∘ₗ t)) ∘ₗ partVal Alg A) ht)
    fun f => mem_part.2 fun v => (t (partVal Alg A f v)).2

end Abstract

section Concrete

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem exists_inf_mul_fin (x : UA E n) : ∃ a ∈ infU E n, ∃ k ∈ finU E n, x = a * k := by
  let y : GL (Fin n) (Cinf E) := cInf x
  have hx : cT (conjAd E) x.1.val * 1 * x.1.val = 1 := x.2
  have h1 : x.1.val.map (pInf E) = y.val := rfl
  have h3 : (cT (conjAd E) x.1.val).map (pInf E) = y.valᴴ := by
    ext1 i j
    rw [Matrix.conjTranspose_apply, ← h1]
    exact (infEq E).symm_apply_apply _
  have hy : y.valᴴ * y.val = 1 := by
    rw [mul_one] at hx
    rw [← h3, ← h1, ← Matrix.map_mul, hx]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  let a : UA E n := ⟨infGL E n y, infGL_mem_UA y hy⟩
  refine ⟨a, pFin_infGL y, a⁻¹ * x, ?_, (mul_inv_cancel_left a x).symm⟩
  have h4 : cInf a = y := pInf_infGL y
  refine MonoidHom.mem_ker.2 ?_
  rw [map_mul, map_inv, h4]
  exact inv_mul_cancel y

theorem stable_of {U : Submodule ℂ (UA E n → ℂ)} (h1 : ∀ x : infU E n, ∀ φ ∈ U, RU E n x.1 φ ∈ U)
    (h2 : ∀ k : finU E n, ∀ φ ∈ U, RU E n k.1 φ ∈ U) (x : UA E n) (φ : UA E n → ℂ) (hφ : φ ∈ U) : RU E n x φ ∈ U := by
  obtain ⟨a, ha, k, hk, rfl⟩ := exists_inf_mul_fin x
  rw [← RU_RU]
  exact h1 ⟨a, ha⟩ _ (h2 ⟨k, hk⟩ _ hφ)

theorem exists_cAll (g : InfinitePlace E → GL (Fin n) ℂ)
    (hg : ∀ v, (g v : Matrix (Fin n) (Fin n) ℂ) ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    ∃ y : infU E n, cAll y.1 = g := by
  classical
  let J : Subgroup (InfinitePlace E → GL (Fin n) ℂ) := (cAll.comp (infU E n).subtype).range
  let Hs : InfinitePlace E → Subgroup (GL (Fin n) ℂ) := fun _ => (GlobalTheory.Branching.unitaryIncl n).range
  have hle : Subgroup.pi Set.univ Hs ≤ J := by
    rw [Subgroup.pi_le_iff]
    intro v
    rintro _ ⟨_, ⟨u, rfl⟩, rfl⟩
    obtain ⟨e, he⟩ := GlobalTheory.T.archimedeanUnitaryPoints_equiv_unitaryGroup E n v.embedding
    let x := e.symm u
    have hx := Subgroup.mem_inf.1 x.2
    refine ⟨⟨x.1, hx.1⟩, ?_⟩
    funext v'
    by_cases h : v' = v
    · subst h
      change cEmb v'.embedding x.1 = _
      rw [← he, e.apply_symm_apply]
      simp
    · have h5 : x.1 ∈ (cEmb (E := E) (n := n) v'.embedding).ker :=
        Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hx.2 v'.embedding) (by simpa using h)
      change cEmb v'.embedding x.1 = _
      rw [MonoidHom.mem_ker.1 h5]
      simp [h]
  obtain ⟨y, hy⟩ : g ∈ J := hle fun v _ => ⟨⟨(g v).val, hg v⟩, Units.ext rfl⟩
  exact ⟨y, hy⟩

theorem span_rep (W : Wt E n) [Nontrivial W.Sp] : Submodule.span ℂ (Set.range W.rep) = ⊤ :=
  GlobalTheory.ClassFin.span_range_eq_top_of_isIrreducible _ _ W.rep ((CuspRep.isIrreducible_iff _).2 ⟨inferInstance, fun U hU =>
    GlobalTheory.CoefIrred.vv_irreducible_unitary (InfinitePlace E) n W U fun g hg x hx => by
      obtain ⟨y, rfl⟩ := exists_cAll g hg
      exact hU y x hx⟩)

def jOf (W : Wt E n) (M : Submodule ℂ (algForms W)) : M →ₗ[ℂ] W.Sp →ₗ[ℂ] (UA E n → ℂ) :=
  (algForms W).subtype ∘ₗ M.subtype

theorem jOf_injective (W : Wt E n) (M : Submodule ℂ (algForms W)) : Function.Injective (jOf W M) :=
  Subtype.val_injective.comp Subtype.val_injective

theorem jOf_rep (W : Wt E n) (M : Submodule ℂ (algForms W)) (p : M) (x : infU E n) (v : W.Sp) :
    jOf W M p (W.rep x v) = RU E n x.1 (jOf W M p v) := p.1.2.2 x v

theorem nontrivial_of_ne_bot {W : Wt E n} {M : Submodule ℂ (algForms W)} (h : M ≠ ⊥) :
    Nontrivial W.Sp ∧ img (jOf W M) ≠ ⊥ := by
  obtain ⟨p, hp, h0⟩ := (Submodule.ne_bot_iff _).1 h
  have h1 : jOf W M ⟨p, hp⟩ ≠ 0 := fun e => h0 (congrArg Subtype.val (jOf_injective W M (e.trans (map_zero _).symm)))
  obtain ⟨v, hv⟩ := DFunLike.ne_iff.1 h1
  refine ⟨⟨v, 0, fun e => hv (by rw [e, map_zero]; rfl)⟩, fun e => hv ?_⟩
  have := apply_mem_img (jOf W M) ⟨p, hp⟩ v
  rw [e, Submodule.mem_bot] at this
  exact this

theorem img_stable {W : Wt E n} {M : Submodule ℂ (algForms W)} (hM : ∀ k, ∀ f ∈ M, algRep W k f ∈ M) (x : UA E n)
    (φ : UA E n → ℂ) (hφ : φ ∈ img (jOf W M)) : RU E n x φ ∈ img (jOf W M) := by
  refine stable_of (fun a => ?_) (fun k => ?_) x φ hφ
  · have h1 : img (jOf W M) ≤ (img (jOf W M)).comap (RU E n a.1) := Submodule.span_le.2 (by
      rintro _ ⟨p, v, rfl⟩
      change RU E n a.1 _ ∈ img (jOf W M)
      rw [← jOf_rep]
      exact apply_mem_img _ _ _)
    exact fun φ hφ => h1 hφ
  · have h1 : img (jOf W M) ≤ (img (jOf W M)).comap (RU E n k.1) := Submodule.span_le.2 (by
      rintro _ ⟨p, v, rfl⟩
      exact apply_mem_img (jOf W M) ⟨algRep W k p.1, hM k _ p.2⟩ v)
    exact fun φ hφ => h1 hφ

theorem V_eq_img (π : AutSub E n) {W : Wt E n} {M : Submodule ℂ (algForms W)} (hM : ∀ k, ∀ f ∈ M, algRep W k f ∈ M)
    (h0 : M ≠ ⊥) (hle : M ≤ π.finPart W) : π.V = img (jOf W M) := by
  have h1 : img (jOf W M) ≤ π.V := Submodule.span_le.2 (by
    rintro _ ⟨p, v, rfl⟩
    exact AutSub.mem_finPart.1 (hle p.2) v)
  exact ((π.isAut.irred _ h1 (img_stable hM)).resolve_left (nontrivial_of_ne_bot h0).2).symm

theorem finPart_stable (π : AutSub E n) (W : Wt E n) : ∀ k, ∀ f ∈ π.finPart W, algRep W k f ∈ π.finPart W :=
  fun k _ h => AutSub.mem_finPart.2 fun v => π.isAut.stable k _ (AutSub.mem_finPart.1 h v)

section Iso

variable {π π' : AutSub E n} {W : Wt E n} (e : π.finPart W ≃ₗ[ℂ] π'.finPart W) (T : π.V ≃ₗ[ℂ] π'.V)
  (hA : π.V = img (jOf W (π.finPart W)))
  (hT : ∀ p v (h : jOf W (π.finPart W) p v ∈ π.V), (T ⟨jOf W (π.finPart W) p v, h⟩ : UA E n → ℂ) = jOf W (π'.finPart W) (e p) v)

include hA hT

end Iso

end Concrete

end GlobalTheory.DefU.Pairs

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowFormMetricEqClassSumMetricStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Df
attribute [local instance] GlobalTheory.Mem.Col2.starE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rowFormMetric_eq_classSumMetric : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (hX : B.fields.Ok) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (F G : (I.per l u a).Mt) (F' G' : MtCx I a), SameForm I l u a F' F → SameForm I l u a G' G → I.ipMt l u a F G = cSum I hX a F' G' := by
  first | exact @GlobalTheory.Mem.Df.ipMt_eq_cSum | exact GlobalTheory.Mem.Df.ipMt_eq_cSum | (intros; apply GlobalTheory.Mem.Df.ipMt_eq_cSum <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SelfIntersectionShift
section
noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions

namespace GlobalTheory.ModelShift

theorem isSelfInter_shift_model : GlobalTheory.Published.ArCalc → GlobalTheory.Published.ArDegree → ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (M : TrueGeo.Model Y) (L : HermLB M.p) (Δ : Y.Dv) (r : (L.B.pull M.j).ι → Y.Fnˣ), Presents Δ (L.B.pull M.j) r → ∀ (t : (𝓞 F →+* ℂ) → ℝ) (ht : ∀ σ, t ((starRingEnd ℂ).comp σ) = t σ) (a : ℝ), (haveI := M.ar.isIntegral; L.IsSelfInter a) → (haveI := M.ar.isIntegral; (L.shift t ht).IsSelfInter (a + ((Y.dim : ℝ) + 1) * (Y.inter (fun _ => Δ) : ℝ) * ∑ σ : F →+* ℂ, t (σ.comp (algebraMap (𝓞 F) F)))) := by
  intro hc hd F _ _ Y M L Δ r hr t ht a ha
  have := M.ar.isIntegral
  let E := Equiv.ofBijective _ (TwistTop.bijective_comp_algebraMap F)
  have key (σ : F →+* ℂ) : (L.φ (σ.comp (algebraMap (𝓞 F) F))).chernInt Y.dim Set.univ (fun _ => 1) =
      (Y.inter (fun _ => Δ) : ℝ) := by
    obtain ⟨Φ, hΦ⟩ := TwistTop.exists_homeomorph F Y M σ
    have := CxPts.secondCountableTopology_of_isProjOver (σ.comp (algebraMap (𝓞 F) F)) M.ar.isProjOver
    obtain ⟨h₁, h₂⟩ := GlobalTheory.chernInt_transfer _ _ _ _ M.p Y.str _ σ Y.dim M.j Φ hΦ
      (GlobalTheory.ModelCharts.genSmooth_model F Y M _) inferInstance _ _ (L.cInf _)
    exact h₂.symm.trans (hd.2 F Y σ Δ _ r hr _ h₁).2
  have e₁ : ∑ᶠ τ, t τ * (L.φ τ).chernInt Y.dim Set.univ (fun _ => 1) =
      (Y.inter (fun _ => Δ) : ℝ) * ∑ σ : F →+* ℂ, t (σ.comp (algebraMap (𝓞 F) F)) := by
    rw [← finsum_comp_equiv E, finsum_eq_sum_of_fintype, Finset.mul_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [show (L.φ (E σ)).chernInt Y.dim Set.univ (fun _ => 1) = _ from key σ, mul_comm]
    rfl
  have h := TwistTop.isSelfInter_shift hc.1 hc.2.1 _ _ _ _ M.ar L a t ht ha
  rw [e₁, ← mul_assoc] at h
  exact h

end GlobalTheory.ModelShift
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SideMultiplicityCharacter
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

noncomputable section

namespace GlobalTheory.HeightCounting.FitTw

variable {D : D7}

set_option maxHeartbeats 2000000 in

def twFL (L : LocAll (lay0 D)) (F : TwFrameC D) : TwFrameC (withLoc L) := { F with }

set_option maxHeartbeats 4000000 in
theorem twTiedL (L : LocAll (lay0 D)) {F : TwFrameC D} {low : Finset ℕ} (h : TwistFrameLowIndexCompatibility D F low) :
    TwistFrameLowIndexCompatibility (withLoc L) (twFL L F) low := { h with }

set_option maxHeartbeats 4000000 in
theorem choiceL (L : LocAll (lay0 D)) {C : NChoice D} (h : ChoiceC D C) : ChoiceC (withLoc L) (chL L C) := { h with }

set_option maxHeartbeats 20000000 in

def mtVL (L : LocAll (lay0 D)) (i : D.ntw.Tw) (j : ℕ) (b : Bool) (k : ℕ) (Q : Finset (PlE D.host))
    (ψ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ) (e : ℤ) (W₀ : Type) [g : AddCommGroup W₀]
    [m : Module (FractionRing (D.ntw.O i)) W₀]
    (ρ₀ : Representation (FractionRing (D.ntw.O i)) (GQ D.host.E D.R.nV) W₀)
    (τ : ∀ kv : (Σ kk : Fin 2, D.nd.PlG kk), (ZMod (D.host.g kv.1))ˣ →* (FractionRing (D.ntw.O i))ˣ)
    (V : NX.MtVReal D i j b k Q ψ e W₀ ρ₀ τ) : @NX.MtVReal (withLoc L) i j b k Q ψ e W₀ g m ρ₀ τ :=
  @NX.MtVReal.mk (withLoc L) i j b k Q ψ e W₀ g m ρ₀ τ V.W V.acg V.mod V.fd V.ρ V.irr V.alg V.bc V.J V.χ V.J_open V.hyp V.QP V.QP_sub V.QP_cover V.QP_nconj V.DP V.DP_sub V.DP_cover V.DP_nconj V.sp V.sp_w V.redG V.J_mem V.chi_eq V.real

set_option maxHeartbeats 4000000 in

def expL (L : LocAll (lay0 D)) (X : NExpTied D) : NExpTied (withLoc L) :=
  { X with
    mtV := fun i j b k Q ψ h1 h2 h =>
      (@mtVL D L i j b k Q ψ X.sgnT (X.Wt i j b) (X.acgWt i j b) (X.modWt i j b) (X.rhoW i j b) (X.tauG i j b) (X.mtV i j b k Q ψ h1 h2 h)) }

set_option maxHeartbeats 4000000 in
theorem nctL {L : LocAll (lay0 D)} {Pl : PlSide D} {M : MtFam D} {C : NChoice D} {big : D.what₂.places.Pl → Finset ℂ}
    (Sp : NdSpec Pl M C big L.X L.T) (h : NChTie D C) : NChTie (withLoc L) (chL L C) where
  twOf_eq := Sp.twOf_eq
  twSide_eq := Sp.twSide_eq
  Q_eq a := (Sp.Q_eq _ _ a ((L.X.locs_mem _ _ a).2 ⟨rfl, rfl⟩)).trans (Sp.Qc_eq _ _)
  psi_eq := by
    obtain ⟨ψ0, h1, h2, -⟩ := h.psi_eq
    exact ⟨ψ0, h1, h2, fun a g => Sp.psi_eq a g _ (h2 _ g)⟩
  embedding_baseField_condition := h.embedding_baseField_condition

set_option maxHeartbeats 4000000 in
theorem chSideL {L : LocAll (lay0 D)} {Pl : PlSide D} {M : MtFam D} {C : NChoice D} {big : D.what₂.places.Pl → Finset ℂ}
    (Sp : NdSpec Pl M C big L.X L.T) {cf : CharFrame D} {X : NExpTied D} {tp : TupTied D cf C}
    (h : ChoiceSide D cf M X C tp) : ChoiceSide (withLoc L) (cfL L cf) (mtL L M) (expL L X) (chL L C) (tpL L tp) where
  nct := nctL Sp h.nct
  choice := choiceL L h.choice
  off := h.off
  adm := h.adm
  psi := h.psi
  eMt_level := h.eMt_level

set_option maxHeartbeats 4000000 in

def chrL {L : LocAll (lay0 D)} {cf : CharFrame D} {jE : D.host.E →+* Qb} {A : SideA D cf jE} {M : MtFam D} {C : NChoice D}
    {tp : TupTied D cf C} {iq : ∀ i : L.X.nd.Loc, FractionRing (L.X.nd.O i) →+* Qbar (L.X.nd.l i)}
    (Au : AutSpec A M tp.tup iq L.Y L.C) : NCharTied (withLoc L) (cfL L cf) (chL L C) (tpL L tp) :=
  { A.chr with muC := Au.muC }

set_option maxHeartbeats 4000000 in

def chiDL (L : LocAll (lay0 D)) (K : NC.NChiData D) (ψ : (withLoc L).nd.Loc → NC.HC D.host.E) : NC.NChiData (withLoc L) :=
  { K with psi := ψ }

set_option maxHeartbeats 4000000 in
theorem chiL (L : LocAll (lay0 D)) {K : NC.NChiData D} (h : NC.NormalizedCharacterCompatibility D K) (ψ : (withLoc L).nd.Loc → NC.HC D.host.E)
    (hψ : ∀ a, NC.ReadC (withLoc L).nd.plOm.1 ((withLoc L).ntw.psiL a) (NC.iotaC (withLoc L) a) (ψ a) 0) :
    NC.NormalizedCharacterCompatibility (withLoc L) (chiDL L K ψ) :=
  { h with psi := hψ }

set_option maxHeartbeats 4000000 in
theorem deltaReadL (L : LocAll (lay0 D)) {cf : CharFrame D} (h : DeltaRead D cf) : DeltaRead (withLoc L) (cfL L cf) := h

set_option maxHeartbeats 8000000 in

theorem nonempty_twOpen : ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : SideA D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C), ChoiceSide D cf M Bs.exp C tp → MtInput D M tp.tup C.Q → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) → (∀ j g, ∃ z : ℤ, eExp D j g = z) → (∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) → GlobalTheory.RowTie.ChebSplit D.nd → ∀ (big : D.what₂.places.Pl → Finset ℂ) (L : LocAll (lay0 D)) (Sp : NdSpec A.pl M C big L.X L.T) (Au : AutSpec A M tp.tup Sp.iq L.Y L.C), Nonempty (TwOpen (withLoc L) (chL L C) (cfL L cf) (tpL L tp) (mtL L M) low) := by
  intro D cf jE A low Pq S hL eig θ Bs M C tp ch _ _ _ _ _ big L Sp Au
  have ch' := chSideL Sp ch
  let K := chiDL L Bs.chiD (fun a => toHC ((tpL L tp).psi ((withLoc L).nd.w a)))
  have h0 : ∀ x, K.etaT.χ x = (cfL L cf).eta.1 x := Bs.eta_eq
  have h1 : ∀ (j : Fin (withLoc L).R.m) x, (K.mu0 (j.1 + 1)).χ x = ((cfL L cf).mu0 j).1 x := Bs.ringSpec_normalisedCharacter_eq
  have h2 : ∀ s x, (K.del s).χ x = ((cfL L cf).delAt ((withLoc L).ntw.l s)).1 x := Bs.del_eq
  have h3 : ∀ a x, (K.psi a).χ x = ((tpL L tp).psi ((withLoc L).nd.w a)).1 x := fun _ _ => rfl
  have hg := psiL_gal' (chrL Au) ch'.nct ch'.psi K h0 h1 h2 Bs.chi.chi1
  have hp := psi_is (tpL L tp) ch'.nct
  exact ⟨{
    chiD := K
    chi := chiL L Bs.chi _ fun a => psiL_read a _ (fun v hv => ((hp a).ram v).2 hv) (hg a)
    twF := twFL L Bs.twF
    tw := twTiedL L Bs.tw
    exp := expL L Bs.exp
    ch := ch'
    eta_eq := h0
    ringSpec_normalisedCharacter_eq := h1
    del_eq := h2
    psi_eq := h3
    etaT_link := etaT_link (chrL Au) _ h0
    muC_link := fun i => Filter.Eventually.of_forall fun w => muC_link (chrL Au) K h1 h2 h3 i w
    iCq_embO := Bs.iCq_embO
    embO_star := Bs.embO_star
    chrN := chrL Au
    chrGal := ⟨hp, hg, deltaReadL L Bs.deltaRead⟩ }⟩

end GlobalTheory.HeightCounting.FitTw

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothVectorsContinuousL2
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR.Mult GlobalTheory.SmVec MeasureTheory Matrix Filter
open scoped TensorProduct ContDiff InnerProductSpace Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SmVec

theorem continuous_toL2_gard : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (P G : Matrix (Fin n) (Fin n) ℂ), IsUnit P → Pᴴ * Formalism.REAL.Jm ε * P = G → IsURepOn (UJset ε) σ → ∀ (X : Type) [TopologicalSpace X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] (ν : Measure X) [IsFiniteMeasure ν] (act : Formalism.REAL.UJ ε → X → X), Continuous (Function.uncurry act) → ∀ (a : H →ₗ[ℂ] (X → ℂ)) (A : H →ₗ[ℂ] Lp ℂ 2 ν), (∀ w ∈ smSub G (trRep σ P), Continuous (a w) ∧ (∃ C : ℝ, ∀ x, ‖a w x‖ ≤ C) ∧ ∀ (g : Formalism.REAL.UJ ε) x, a (σ (umat g) w) x = a w (act g x)) → (∀ x, Sobolev₂ (lieG G) (trRep σ P) ((LinearMap.proj x).comp a)) → (∀ w ∈ smSub G (trRep σ P), (A w : X → ℂ) =ᵐ[ν] a w) → ∀ φ, IsTest φ → Continuous fun w => A (gard ε σ φ w) := by
  intro n ε H _ _ _ σ P G hP hG hσ X _ _ _ _ ν _ act _ a A _ hs hA φ hφ
  let g := GlobalTheory.LowTypeRestriction.garding hσ hφ.continuous hφ.2
  have hg : ∀ w, gard ε σ φ w = g w := fun w => gard_eq hσ hφ w
  let L : H →ₗ[ℂ] Lp ℂ 2 ν := A.comp (g : H →ₗ[ℂ] H)
  have hL : ∀ w, L w = A (gard ε σ φ w) := fun w => rfl
  have hc : ∀ x, Continuous fun w => a (gard ε σ φ w) x := fun x => by
    obtain ⟨C, hC⟩ := (GlobalTheory.T.sobolevContinuous_form_gardingVector n ε H σ P G hP hG hσ _ (hs x)).1 φ hφ
    exact (LinearMap.mkContinuous (((LinearMap.proj x).comp a).comp (g : H →ₗ[ℂ] H)) C hC).continuous
  have key : Continuous L := by
    refine L.continuous_of_seq_closed_graph fun u w f hu hf => ?_
    obtain ⟨ns, hns, hae⟩ := (tendstoInMeasure_of_tendsto_Lp hf).exists_seq_tendsto_ae
    have h1 : ∀ᵐ x ∂ν, ∀ k, (L (u k) : X → ℂ) x = a (gard ε σ φ (u k)) x :=
      ae_all_iff.2 fun k => hA _ (gard_mem hP hG hσ hφ (u k))
    refine Lp.ext ?_
    filter_upwards [hae, h1, hA _ (gard_mem hP hG hσ hφ w)] with x hx h1x h2x
    have h3 : Tendsto (fun k => a (gard ε σ φ (u (ns k))) x) atTop (𝓝 (a (gard ε σ φ w) x)) :=
      ((hc x).tendsto w).comp (hu.comp hns.tendsto_atTop)
    have h4 : Tendsto (fun k => a (gard ε σ φ (u (ns k))) x) atTop (𝓝 (f x)) :=
      hx.congr fun k => h1x (ns k)
    exact (tendsto_nhds_unique h4 h3).trans h2x.symm
  exact key

end GlobalTheory.SmVec
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceOutsideNonHyperspecialOfLocalisation
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

noncomputable section

namespace GlobalTheory.SplitOutPlace

set_option maxHeartbeats 1000000 in

theorem not_mem_gPl_qPl : ∀ (D : D7) (cf : CharFrame D) (C : NChoice D) (tp : TupTied D cf C) (Pl : PlSide D) (M : MtFam D) (big : D.what₂.places.Pl → Finset ℂ) (X : LocNd (lay0 D)) (T : LocTw X) (Sp : NdSpec Pl M C big X T) (i : X.nd.Loc) (w : PlE D.host) (s : SplitPlace D.host.E), SplitOut X.nd i w → IsConjPl D.host w s.w → s.v ∉ gPl D ∪ qPl D (tp.tup (D.what₂.muTw (X.nd.w i)) ⟨X.nd.j i - 1, by have := X.nd.j_range i; omega⟩) := by
  intro D cf C tp Pl M big X T Sp i w s hso hc hmem
  obtain ⟨-, hl, hS, hQ⟩ := hso

  have hp : ∀ (w' : PlE D.host), NG.OverPl w' s.v → ∀ p : ℕ, w' ∈ placesOver D.host.E p →
      w ∈ placesOver D.host.E p := by
    intro w' hover p hp
    have h1 : algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E) (p : 𝓞 (maximalRealSubfield D.host.E)) ∈
        w'.asIdeal := by rw [map_natCast]; exact hp
    have h2 : (p : 𝓞 (maximalRealSubfield D.host.E)) ∈ s.v.asIdeal := by
      rw [← hover]; exact h1
    have h3 : algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E) (p : 𝓞 (maximalRealSubfield D.host.E)) ∈
        s.w.asIdeal := by
      rw [← Ideal.mem_comap, s.w_under]; exact h2
    rw [map_natCast] at h3
    exact (hc (p : 𝓞 D.host.E) (p : 𝓞 D.host.E) (by simp)).2 h3
  have hi : i ∈ X.nd.locs (X.nd.j i) (X.nd.w i) := (X.nd.locs_mem _ _ i).2 ⟨rfl, rfl⟩
  have hg : s.v ∉ gPl D := by
    rintro ⟨w', hover, k, hk⟩
    apply hS
    refine (X.nd.S_def i w).2 ⟨?_, hl⟩
    have hw := hp w' hover _ hk
    fin_cases k
    · exact Or.inl hw
    · exact Or.inr (Or.inl hw)
  rcases hmem with hm | hm
  · exact hg hm
  obtain ⟨w', hover, hw'⟩ := GlobalTheory.FitHecke.qPl_sub tp (X.nd.w i) (X.nd.w_tw i)
    ⟨X.nd.j i - 1, by have := X.nd.j_range i; omega⟩ hm
  rcases hw' with hCQ | hpd
  · apply hQ
    rw [← Sp.Qc_eq (X.nd.j i) (X.nd.w i)] at hCQ
    have hsw : s.w ∈ Sp.B.Qc (X.nd.j i) (X.nd.w i) :=
      Sp.B.Qc_over (X.nd.j i) (X.nd.w i) w' s.w hCQ ⟨s.v, hover, s.w_under⟩
    rw [Sp.Q_eq _ _ i hi]
    exact Sp.B.Qc_conj (X.nd.j i) (X.nd.w i) w s.w hsw hc
  · apply hS
    refine (X.nd.S_def i w).2 ⟨?_, hl⟩
    rw [X.nd.w_l i] at hpd
    exact Or.inr (Or.inr (hp w' hover _ hpd))

end GlobalTheory.SplitOutPlace
end
end

