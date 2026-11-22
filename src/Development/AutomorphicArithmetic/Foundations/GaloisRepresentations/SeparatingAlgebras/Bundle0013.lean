import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.Bundle0010
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0216
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0192
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0195

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.OpOfSmul
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU

namespace UpperTheory.Gal.Gen

open GlobalTheory.CongW (IntMat wtSize HasTypeVec IsIntegralOpW)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a : ℕ}

theorem opOf_smul' (c : ℂ) (f : UA E a →₀ ℂ) (φ : UA E a → ℂ) : opOf (RU E a) (c • f) φ = c • opOf (RU E a) f φ := by
  have e : ∀ f : UA E a →₀ ℂ, opOf (RU E a) f φ = Finsupp.linearCombination ℂ (fun g => RU E a g φ) f := fun f =>
    (Finsupp.linearCombination_apply ℂ f).symm
  rw [e, e, map_smul]

theorem core (hT : ToPolyX) (hC : Combine) (hR : Restrict) {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ)
    (w₀ : HeightOneSpectrum (𝓞 E)) (K : Subgroup (UA E a)) (hK : K ≤ finU E a) (lam : (E →+* ℂ) → DomWeight a)
    (S : Type) [Fintype S] (Gn : S → Submodule ℂ (UA E a → ℂ) → Prop) (P : Submodule ℂ (UA E a → ℂ) → Prop)
    (hG : Dense ι (Wt.ofFam lam) K fun U => ∀ w, Gn w U) (hP : Dense ι (Wt.ofFam lam) K P)
    (J : Type) (t : J → (UA E a →₀ ℂ)) (η : Submodule ℂ (UA E a → ℂ) → J → ℂ) (hact : ActsBy K t η)
    (f : S → (UA E a →₀ ℂ)) (e : S → Submodule ℂ (UA E a → ℂ) → ℂ)
    (hf : ∀ w U, IsAutRepU U → (∀ φ ∈ U, (∀ x ∈ K, RU E a x φ = φ) → opOf (RU E a) (f w) φ = e w U • φ) ∧
        ((∃ φ ∈ U, φ ≠ 0 ∧ ∀ x ∈ K, RU E a x φ = φ) → (e w U ≠ 0 ↔ Gn w U)))
    (hF : FramedX ι (Wt.ofFam lam) (Sum.elim t f)) (U : Submodule ℂ (UA E a → ℂ)) (hU : OfType lam K U) :
    PolyApprox (fun j => ι.symm (η U j))
      {θ | ∃ U', OfType lam K U' ∧ P U' ∧ (∀ w, Gn w U') ∧ θ = fun j => ι.symm (η U' j)} := by
  classical
  let η' : Submodule ℂ (UA E a → ℂ) → J ⊕ S → ℂ := fun U => Sum.elim (η U) fun w => e w U
  have hact' : ActsBy K (Sum.elim t f) η' := by
    intro U hU φ hφ hfix j
    cases j with
    | inl j => exact hact U hU φ hφ hfix j
    | inr w => exact (hf w U hU).1 φ hφ hfix
  let Q : MvPolynomial (J ⊕ S) ℤ := ∏ w : S, MvPolynomial.X (Sum.inr w)
  have hQ : ∀ U', OfType lam K U' → (MvPolynomial.aeval (fun j => ι.symm (η' U' j)) Q ≠ 0 ↔ ∀ w, Gn w U') := by
    intro U' hU'
    simp only [Q, map_prod, MvPolynomial.aeval_X, Finset.prod_ne_zero_iff, Finset.mem_univ, true_imp_iff]
    refine forall_congr' fun w => ?_
    rw [← (hf w U' hU'.aut).2 hU'.fix]
    exact map_ne_zero_iff _ ι.symm.injective
  have h1 := hT E l ι a w₀ K hK lam _ hG _ _ η' hF hact' U hU
  have h2 := hC (Qbar l) _ _ _ {θ | ∃ U', OfType lam K U' ∧ P U' ∧ θ = fun j => ι.symm (η' U' j)} Q h1 (by
    rintro _ ⟨U', hU', hg, rfl⟩
    exact ⟨(hQ U' hU').2 hg, hT E l ι a w₀ K hK lam _ hP _ _ η' hF hact' U' hU'⟩)
  refine (hR (Qbar l) J _ Sum.inl _ _ h2).mono ?_
  rintro _ ⟨_, ⟨⟨U', hU', hp, rfl⟩, hq⟩, rfl⟩
  exact ⟨U', hU', hp, (hQ U' hU').1 hq, rfl⟩

theorem genW_of (hT : ToPolyX) (hC : Combine) (hR : Restrict) (hD : DenseGen) (hO : TestOp) (hS : ScaleW) (hF : FrameW) :
    GenW := by
  intro E _ _ _ l _ ι a ha w₀ hl hs K hK lam S Φ hd P hP J t η ht hact U hU
  obtain ⟨W, -, hW, -⟩ := GlobalTheory.T.exists_algebraicForm_weight_level_smooth_at_place E a lam K U hK.fin hU w₀
  have hlam : (Wt.ofFam lam).at = lam := by
    obtain rfl : lam = W.at := (funext hW).symm
    have : Wt.ofFam W.at = W := funext fun v => W.at_embedding v
    rw [this]
  choose f e hfin hf using fun w : S => hO E a K w.1 (hd.split w.1 w.2) (hd.hyp w.1 w.2) (Φ w.1)
  choose c hc0 hc using fun w : S => hS E l ι a lam (f w) (hfin w)
  have hG : Dense ι (Wt.ofFam lam) K fun U => ∀ w : S, GenAt w.1 (Φ w.1) U := by
    have := hD E l ι a ha w₀ hl hs K hK (Wt.ofFam lam) S Φ hd
    simpa only [Subtype.forall] using this
  have := core hT hC hR ι w₀ K hK.fin lam S (fun w U => GenAt w.1 (Φ w.1) U) P hG hP J t η hact (fun w => c w • f w)
    (fun w U => c w * e w U) (fun w U hU => ⟨fun φ hφ hx => by rw [opOf_smul', (hf w U hU).1 φ hφ hx, smul_smul], fun h => by
      rw [← (hf w U hU).2 h]; simp [hc0 w]⟩)
    (hF E l ι a _ _ _ fun j => by
      rw [hlam]
      cases j with
      | inl j => exact ht j
      | inr w => exact hc w) U hU
  simpa only [Subtype.forall] using this

theorem genP_of (hT : ToPolyX) (hC : Combine) (hR : Restrict) (hD : DenseGen) (hO : TestOp) (hF : FrameOps) : GenP := by
  intro E _ _ _ l _ ι a ha w₀ hl hs K hK lam S Φ hd P hP J t η ht hact
  choose f e hfin hf using fun w : S => hO E a K w.1 (hd.split w.1 w.2) (hd.hyp w.1 w.2) (Φ w.1)
  obtain ⟨c, hc, hfr⟩ := hF E l ι a (Wt.ofFam lam) (J ⊕ S) (Sum.elim t f) fun j => by
    cases j with
    | inl j => exact ht j
    | inr w => exact hfin w
  refine ⟨fun j => c (Sum.inl j), fun j h => hc (Sum.inl j) h, fun U hU => ?_⟩
  have hl0 : (l : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  have hG : Dense ι (Wt.ofFam lam) K fun U => ∀ w : S, GenAt w.1 (Φ w.1) U := by
    have := hD E l ι a ha w₀ hl hs K hK (Wt.ofFam lam) S Φ hd
    simpa only [Subtype.forall] using this
  have := core hT hC hR ι w₀ K hK.fin lam S (fun w U => GenAt w.1 (Φ w.1) U) P hG hP J
    (fun j => (l : ℂ) ^ c (Sum.inl j) • t j) (fun U j => (l : ℂ) ^ c (Sum.inl j) * η U j)
    (fun U hU φ hφ hx j => by rw [opOf_smul', hact U hU φ hφ hx j, smul_smul])
    (fun w => (l : ℂ) ^ c (Sum.inr w) • f w)
    (fun w U => (l : ℂ) ^ c (Sum.inr w) * e w U)
    (fun w U hU => ⟨fun φ hφ hx => by rw [opOf_smul', (hf w U hU).1 φ hφ hx, smul_smul], fun h => by
      rw [← (hf w U hU).2 h]; simp [hl0]⟩)
    (by
      convert hfr.framedX using 2 with j
      cases j <;> rfl) U hU
  simpa only [Subtype.forall, map_mul, map_pow, map_natCast] using this

theorem part_mono (W : Wt E a) (C : Subgroup (UA E a)) {P Q : Submodule ℂ (UA E a → ℂ) → Prop} (h : ∀ U, P U → Q U) :
    part W C P ≤ part W C Q :=
  iSup₂_le fun π hπ => le_iSup₂_of_le (f := fun (π : AutSub E a) (_ : Q π.V) => π.finPart W ⊓ fixedBy W C) π (h _ hπ) le_rfl

theorem genTyL_of (hW : GenW) (hH : HypOf) (hSm : SmoothAt) (hL : LevFacts) (hTy : TyStep) : GlobalTheory.CongW.GenTyL := by
  intro E _ _ _ l _ ι a ha w₀ hl hs K hK lam Jx t η ht hact Fam hFam hcof S hS D _ hD0 U hU
  have hd : GenData w₀ K S fun _ => MvPolynomial.map (Int.castRingHom ℂ) D :=
    ⟨fun w hw => (hS w hw).1, fun w hw => (hS w hw).2.1, fun w hw => hH E a K hK.compact w (hS w hw).1 (hS w hw).2.2,
      fun _ _ h => hD0 (MvPolynomial.map_injective _ Int.cast_injective (h.trans (map_zero _).symm))⟩
  have hl1 : ‖((l : ℕ) : Qbar l)‖ < 1 := by
    have h := PadicAlgCl.norm_extends l (l : ℚ_[l])
    rw [map_natCast] at h
    rw [h, Padic.norm_p]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt)
  refine (hW E l ι a ha w₀ hl hs K hK lam S _ hd (fun U' => ∃ (J : Subgroup (GL (Fin a) (w₀.adicCompletion E))) (m : ℕ)
    (θ : J →* Multiplicative (ZMod (l ^ m))), Fam J m θ ∧ ∃ χ : Multiplicative (ZMod (l ^ m)) →* ℂˣ, χ ≠ 1 ∧
      HasTypeVec w₀ K J θ χ U') ?_ Jx t η (fun j => intW_of (ht j)) hact U hU).mono ?_
  · intro f hf ε hε
    obtain ⟨N, hN, hfN⟩ := hSm E a w₀ hs _ f
    obtain ⟨m₀, hm₀⟩ := exists_pow_lt_of_lt_one hε hl1
    obtain ⟨J, m, θ, hm, hJN, hF⟩ := hcof (interior N) isOpen_interior (mem_interior_iff_mem_nhds.2 hN) m₀
    obtain ⟨hJo, hJc, hJt, -⟩ := hFam J m θ hF
    have hfJ : f ∈ fixedBy (Wt.ofFam lam) (lev K w₀ J) := by
      intro c hc v g
      obtain ⟨k, hk, x, hx, hxJ, rfl⟩ := ((hL E a w₀ hs K hK J hJo hJc).2.1 c).1 hc
      rw [← mul_assoc, hfN x hx (interior_subset (hJN hxJ)), hf k hk]
    obtain ⟨G, hG, e, he, hGe⟩ := hTy E l ι a w₀ hs K hK _ J hJo hJc hJt m θ f hfJ
    exact ⟨G, part_mono _ _ (fun U h => ⟨J, m, θ, hF, h⟩) hG, e, fun g => (he g).trans
      ((pow_le_pow_of_le_one (norm_nonneg _) hl1.le hm).trans hm₀.le), hGe⟩
  · rintro _ ⟨U', h1, h2, h3, rfl⟩
    refine ⟨U', h1, h2, fun w hw σ hσ B hB α hα => ?_, rfl⟩
    have := h3 w hw α ⟨σ, hσ, hα ▸ hB⟩
    rw [MvPolynomial.eval_map] at this
    rw [MvPolynomial.aeval_def]
    exact this

end UpperTheory.Gal.Gen

end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.SizeLe
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU
open UpperTheory.Gal.Gen

namespace UpperTheory.Gal.Gen.SeparatingAlgebraSizeBound

private def sz {a : ℕ} (lam : DomWeight a) : ℕ := ∑ k, (lam.w k).natAbs

private theorem sz_dual {a : ℕ} (lam : DomWeight a) : sz lam.dual = sz lam := by
  unfold sz DomWeight.dual
  simp only [Int.natAbs_neg]
  exact Fintype.sum_equiv Fin.revPerm _ _ (fun k => by simp)

private theorem one_le {a : ℕ} (lam : DomWeight a) :
    ∑ i, lam.natW i + a * lam.detShift.natAbs ≤ a * (2 * sz lam) := by
  have key : ∀ i : Fin a, lam.natW i + lam.detShift.natAbs ≤ 2 * sz lam := by
    intro i
    have ha : 0 < a := i.pos
    have hd : lam.detShift = lam.w ⟨a - 1, by omega⟩ := by
      simp only [DomWeight.detShift, dif_pos ha]
    have hnat : lam.natW i = (lam.w i - lam.w ⟨a - 1, by omega⟩).toNat := by
      simp only [DomWeight.natW, hd]
    have hLle : (lam.w ⟨a - 1, by omega⟩).natAbs ≤ sz lam := by
      unfold sz
      exact Finset.single_le_sum (f := fun k => (lam.w k).natAbs) (fun k _ => Nat.zero_le _)
        (Finset.mem_univ _)
    rw [hnat, hd]
    by_cases hi : i = ⟨a - 1, by omega⟩
    · have h0 : (lam.w i - lam.w ⟨a - 1, by omega⟩).toNat = 0 := by
        rw [hi, sub_self]; rfl
      omega
    · have hpair : (lam.w i).natAbs + (lam.w ⟨a - 1, by omega⟩).natAbs ≤ sz lam := by
        unfold sz
        have h := Finset.sum_le_sum_of_subset_of_nonneg (f := fun k => (lam.w k).natAbs)
          (Finset.subset_univ {i, ⟨a - 1, by omega⟩}) (fun _ _ _ => Nat.zero_le _)
        rwa [Finset.sum_pair hi] at h
      omega
  calc ∑ i, lam.natW i + a * lam.detShift.natAbs
      = ∑ i, (lam.natW i + lam.detShift.natAbs) := by
        simp [Finset.sum_add_distrib]
    _ ≤ ∑ _i : Fin a, 2 * sz lam := Finset.sum_le_sum fun i _ => key i
    _ = a * (2 * sz lam) := by simp

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a : ℕ}

private noncomputable def emb : InfinitePlace E ⊕ InfinitePlace E → (E →+* ℂ)
  | .inl v => v.embedding
  | .inr v => ComplexEmbedding.conjugate v.embedding

private theorem mk_emb_inl (v : InfinitePlace E) : InfinitePlace.mk (emb (.inl v)) = v :=
  InfinitePlace.mk_embedding v

private theorem mk_emb_inr (v : InfinitePlace E) : InfinitePlace.mk (emb (.inr v)) = v := by
  simp [emb]

private theorem emb_injective : Function.Injective (emb (E := E)) := by
  intro x y h
  have hm : InfinitePlace.mk (emb x) = InfinitePlace.mk (emb y) := by rw [h]
  rcases x with v | v <;> rcases y with w | w <;>
    simp only [mk_emb_inl, mk_emb_inr] at hm <;> subst hm
  · rfl
  · simp only [emb] at h
    exact absurd h.symm (conjugate_ne _)
  · simp only [emb] at h
    exact absurd h (conjugate_ne _)
  · rfl

private theorem two_le (W : Wt E a) : ∑ v, 2 * sz (W v) ≤ GlobalTheory.CongW.wtSize W.at := by
  have h1 : ∑ v, 2 * sz (W v)
      = ∑ s : InfinitePlace E ⊕ InfinitePlace E, sz (W.at (emb s)) := by
    rw [Fintype.sum_sum_type]
    simp only [emb, Wt.at_embedding, Wt.at_conjugate, sz_dual, two_mul, Finset.sum_add_distrib]
  have h2 : ∑ s : InfinitePlace E ⊕ InfinitePlace E, sz (W.at (emb s))
      = ∑ τ ∈ Finset.univ.map ⟨emb, emb_injective⟩, sz (W.at τ) := by
    rw [Finset.sum_map]; rfl
  have h3 : GlobalTheory.CongW.wtSize W.at = ∑ τ, sz (W.at τ) := rfl
  rw [h1, h2, h3]
  exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)

end UpperTheory.Gal.Gen.SeparatingAlgebraSizeBound

open UpperTheory.Gal.Gen.SeparatingAlgebraSizeBound in
theorem UpperTheory.Gal.Gen.sizeLe_pf :
    UpperTheory.Gal.Gen.SizeLe := by
  intro E _ _ _ a W
  calc (∑ v, ∑ i, (W v).natW i) + ∑ v, a * (W v).detShift.natAbs
      = ∑ v, (∑ i, (W v).natW i + a * (W v).detShift.natAbs) := Finset.sum_add_distrib.symm
    _ ≤ ∑ v, a * (2 * sz (W v)) := Finset.sum_le_sum fun v _ => one_le (W v)
    _ = a * ∑ v, 2 * sz (W v) := by rw [Finset.mul_sum]
    _ ≤ a * GlobalTheory.CongW.wtSize W.at := Nat.mul_le_mul_left a (two_le W)
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.TotalDegreeLeOfCol
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU
open UpperTheory.Gal.Gen

private theorem totalDegree_le_of_col {r n : ℕ} {ν : Fin n → ℕ} {F : MvPolynomial (Fin r × Fin n) ℂ}
    (h : MvPolynomial.IsWeightedHomogeneous (Formalism.GradedWeylDivisibility.colW r n) F ν) : F.totalDegree ≤ ∑ i, ν i := by
  unfold MvPolynomial.totalDegree
  refine Finset.sup_le fun m hm => ?_
  have hw : Finsupp.weight (Formalism.GradedWeylDivisibility.colW r n) m = ν := h (MvPolynomial.mem_support_iff.mp hm)
  rw [← hw, Finsupp.weight_apply]
  simp only [Finsupp.sum, Finset.sum_apply, Pi.smul_apply, Formalism.GradedWeylDivisibility.colW, smul_eq_mul]
  rw [Finset.sum_comm]
  refine le_of_eq (Finset.sum_congr rfl fun v _ => ?_)
  simp [Pi.single_apply]

theorem UpperTheory.Gal.Gen.degLe_pf :
    UpperTheory.Gal.Gen.DegLe := by
  intro T _ n lam x hx
  refine Submodule.span_induction (p := fun x _ => MvPolynomial.totalDegree x ≤ ∑ τ, ∑ i, (lam τ).natW i)
    ?_ ?_ ?_ ?_ hx
  · rintro P ⟨F, hF, rfl⟩
    refine (MvPolynomial.totalDegree_finset_prod _ _).trans (Finset.sum_le_sum fun τ _ => ?_)
    refine (MvPolynomial.totalDegree_rename_le (fun v => (τ, v)) (F τ)).trans ?_
    have hm := (Submodule.mem_inf.mp (hF τ)).1
    exact totalDegree_le_of_col ((MvPolynomial.mem_weightedHomogeneousSubmodule _ _ _ _).mp hm)
  · simp
  · intro a b _ _ ha hb
    exact (MvPolynomial.totalDegree_add a b).trans (max_le ha hb)
  · intro c a _ ha
    exact (MvPolynomial.totalDegree_smul_le c a).trans ha
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.TyStep
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU
open UpperTheory.Gal.Gen

theorem UpperTheory.Gal.Gen.tyStep_pf :
    UpperTheory.Gal.Gen.LevFacts → UpperTheory.Gal.Gen.Ell → UpperTheory.Gal.Gen.KerOpen → UpperTheory.Gal.Gen.CharSum → UpperTheory.Gal.Gen.TwistPart → UpperTheory.Gal.Gen.TyStep := by
  intro hLev hEll hKer hCS hTw E _ _ _ l _ ι a w₀ hs K hK W J hJo hJc htf m θ f hf
  classical
  obtain ⟨hLvl, -, hC, -, -, -⟩ := hLev E a w₀ hs K hK J hJo hJc
  haveI : NeZero (l ^ m) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  haveI : Finite (Multiplicative (ZMod (l ^ m))) :=
    inferInstanceAs (Finite (ZMod (l ^ m)))
  let lam : (lev K w₀ J) →* Multiplicative (ZMod (l ^ m)) :=
    θ.comp (((cLoc w₀).comp (lev K w₀ J).subtype).codRestrict J fun c => hC c.1 c.2)
  have hlam : ∀ c : lev K w₀ J, lam c = θ ⟨cLoc w₀ c.1, hC c.1 c.2⟩ := fun c => rfl
  obtain ⟨N, hNo, hN1, hN⟩ := hKer E w₀ a J hJo _ θ
  obtain ⟨ℓ, hℓi, hℓC, hℓa⟩ := hEll E a (lev K w₀ J) hLvl _ lam
    ⟨cLoc w₀ ⁻¹' N, hNo.preimage (GlobalTheory.BCT.GlobLev.continuous_cLoc w₀), by simpa using hN1,
      fun c hc => hN ⟨cLoc w₀ c.1, hC c.1 c.2⟩ hc⟩
    (fun c hc => by
      obtain ⟨k, hk0, hk⟩ := isOfFinOrder_iff_pow_eq_one.1 hc
      have h1 : (cLoc w₀ c.1) ^ k = 1 := by
        have h0 : c.1 ^ k = 1 := by simpa using congrArg Subtype.val hk
        rw [← map_pow, h0, map_one]
      have h2 := htf _ (hC c.1 c.2) k hk0 h1
      have h3 : (⟨cLoc w₀ c.1, hC c.1 c.2⟩ : J) = 1 := Subtype.ext h2
      rw [hlam, h3, map_one])
  obtain ⟨s, hs1, hs2⟩ := hCS (l ^ m)
  have hex : ∀ χ : Multiplicative (ZMod (l ^ m)) →* ℂˣ,
      ∃ F : algForms W, ∀ v g, F.1 v g = ((χ (ℓ g) : ℂˣ) : ℂ) * f.1 v g := fun χ =>
    GlobalTheory.T.exists_algebraicModularForm_mul_archInvariant E a W f (fun g => ((χ (ℓ g) : ℂˣ) : ℂ)) (hℓa fun y => ((χ y : ℂˣ) : ℂ))
      fun g x hx => by simp only [hℓi g x hx]
  choose F hF using hex
  have hpart : ∀ χ ∈ s, F χ ∈ part W K
      (fun U => ∃ χ : Multiplicative (ZMod (l ^ m)) →* ℂˣ, χ ≠ 1 ∧ GlobalTheory.CongW.HasTypeVec w₀ K J θ χ U) := by
    intro χ hχ
    have h := hTw E a w₀ K W J _ θ χ hC (fun k hk => hK.one k hk w₀ (not_apart_self w₀)) (F χ)
      (fun c hc v g => by
        rw [hF, hF, hℓC g ⟨c, hc⟩, hf c hc v g, map_mul, Units.val_mul, hlam, mul_comm (((χ (ℓ g) : ℂˣ) : ℂ))]
        ring)
    refine (?_ : part W K _ ≤ part W K _) h
    exact iSup₂_le fun π hπ => le_iSup₂_of_le π ⟨χ, hs1 χ hχ, hπ⟩ le_rfl
  refine ⟨-∑ χ ∈ s, F χ, neg_mem (sum_mem hpart), fun g => 1 + ∑ χ ∈ s, ((χ (ℓ g) : ℂˣ) : ℂ), ?_, ?_⟩
  · intro g
    rcases hs2 (ℓ g) with h | h
    · simp only [h, map_zero, norm_zero]
      positivity
    · simp only [h]
      rw [map_natCast, Nat.cast_pow, norm_pow]
  · intro v g
    have e : ((-∑ χ ∈ s, F χ : algForms W) : W.Sp →ₗ[ℂ] (UA E a → ℂ)) v g = -∑ χ ∈ s, (F χ).1 v g := by
      simp [Finset.sum_apply, LinearMap.sum_apply]
    change f.1 v g - ((-∑ χ ∈ s, F χ : algForms W) : W.Sp →ₗ[ℂ] (UA E a → ℂ)) v g = _
    rw [e, Finset.sum_congr rfl fun χ _ => hF χ v g, ← Finset.sum_mul]
    ring
end

