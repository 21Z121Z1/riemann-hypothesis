import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0777
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0838
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0842
import Formalism.LocalToGlobal.Columns.RowFormsLemmas
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0764
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlkGLOneCorner
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0067
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero
import Formalism.MeanHeightDescent.DivisionInequalityWithCovolume
import Formalism.LocalRingCardinality.Lemmas
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SlopeSqSubLeSlopeSqSpan
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0787
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0841
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterSumLocalConstantTenth
section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder

namespace GlobalTheory.ChainClassNumbers

theorem card_orbits_le_principal {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}
    {ST SG : Finset (HeightOneSpectrum (𝓞 E))} {G' D' : Type} [Group G'] [MulAction G' D']
    (p : D' → DecoSet E n ST SG) (hp : Function.Injective p)
    (h : ∀ (g : UF E n) (x : D'), ∃ g' : G', p (g' • x) = (g, (1 : GLG E n SG)) • p x)
    [Finite (MulAction.orbitRel.Quotient ((⊤ : Subgroup (UF E n)).prod (⊥ : Subgroup (GLG E n SG))) (DecoSet E n ST SG))] :
    Nat.card (MulAction.orbitRel.Quotient G' D') ≤
      Nat.card (MulAction.orbitRel.Quotient ((⊤ : Subgroup (UF E n)).prod (⊥ : Subgroup (GLG E n SG))) (DecoSet E n ST SG)) := by
  refine Nat.card_le_card_of_injective
    (fun c : MulAction.orbitRel.Quotient G' D' =>
      (Quotient.mk (MulAction.orbitRel _ _) (p (Quotient.out c)) :
        MulAction.orbitRel.Quotient ((⊤ : Subgroup (UF E n)).prod (⊥ : Subgroup (GLG E n SG))) (DecoSet E n ST SG))) ?_
  intro c c' hcc
  obtain ⟨⟨⟨g, k⟩, hgk⟩, hg⟩ := Quotient.exact hcc
  have hk : k = 1 := (Subgroup.mem_prod.1 hgk).2
  subst hk
  obtain ⟨g', hg'⟩ := h g (Quotient.out c')
  have he : g' • Quotient.out c' = Quotient.out c := hp (hg'.trans hg)
  rw [← Quotient.out_eq c, ← Quotient.out_eq c']
  exact Quotient.sound ⟨g', he⟩

theorem card_orbits_le_exp {D : D7} {N : NumDatum} {X : Fields} {s : Seam D X} {Pr : Primes X} (hH : HostTie N s Pr)
    (pl : RPl N.R ≃ X.Tau) (u : Pr.Word) {δ : Code N} (hS : SizeRows N δ (Pr.T u)) {n : ℕ} (hn : 1 ≤ n) (hnN : n ≤ N.Nm)
    {ST SG : Finset (HeightOneSpectrum (𝓞 X.E))} (hST : ST ⊆ Pr.vT u) (hSG : SG = Pr.vGs)
    {G' D' : Type} [Group G'] [MulAction G' D'] (p : D' → DecoSet X.E n ST SG) (hp : Function.Injective p)
    (h : ∀ (g : UF X.E n) (x : D'), ∃ g' : G', p (g' • x) = (g, (1 : GLG X.E n SG)) • p x) :
    (Nat.card (MulAction.orbitRel.Quotient G' D') : ℝ) ≤ Real.exp (55 * errUnit N (Pr.T u)) := by
  have hrdE := hH.rd_eq
  obtain ⟨hR, hq, hd, -, -, -, hX, -, -, hP, -, -, hg, -⟩ := hH
  obtain ⟨⟨s1, -⟩, s2, -, s4, -⟩ := hS
  obtain ⟨hfin, hcount⟩ := GlobalTheory.DecoClassCount.card_classes_le X hX.ok n ST SG
  have hle := card_orbits_le_principal p hp h
  have hk : 5 ≤ N.R.k := by have := N.R.m_add_three_le_k; have := N.R.two_le_m; omega
  have hf : X.f = N.R.f := by
    have h1 : X.f = Nat.card X.Tau := Nat.card_eq_fintype_card.symm
    rw [h1, ← Nat.card_congr pl, Nat.card_prod, Nat.card_eq_fintype_card (α := N.R.A), N.R.card_A]
    simp [Ranks.f, Ranks.n]
  have hE : Module.finrank ℚ X.E = 2 * N.R.f := by
    have h1 := Module.finrank_mul_finrank ℚ X.F X.E
    rw [hX.ok.rankE, ← hX.ok.card_Tau] at h1
    rw [← hf, mul_comm]
    exact h1.symm
  have hf1 : 1 ≤ N.R.f := hf ▸ hX.ok.f_pos
  have hfib := GlobalTheory.ColumnClassLog.fibre_bound_le hP u n hn SG hSG
  rw [hf, hg 0, hg 1] at hfib
  have hsub : ∏ P ∈ ST, Ideal.absNorm P.asIdeal ^ n ≤ ∏ P ∈ Pr.vT u, Ideal.absNorm P.asIdeal ^ n := by
    refine Finset.prod_le_prod_of_subset_of_one_le' hST fun P hP' _ => ?_
    rw [hP.vT_norm u P hP']
    exact Nat.one_le_pow _ _ (hP.T_prime u).pos
  have hfib' := (Nat.mul_le_mul_right _ hsub).trans hfib
  have hrd : |(discr X.E : ℝ)| ^ ((1 : ℝ) / (Module.finrank ℚ X.E : ℝ)) = N.rd := by
    have e : X.E ≃ₐ[ℚ] D.host.E := s.iE.toRatAlgEquiv
    have h1 : D.host.rdE = N.rd := hrdE.symm
    rw [discr_eq_discr_of_algEquiv X.E e, e.toLinearEquiv.finrank_eq]
    exact h1
  have hrd0 : 0 < N.rd := by
    rw [← hrd]
    exact Real.rpow_pos_of_pos (abs_pos.2 (by exact_mod_cast discr_ne_zero _)) _
  have hL : 1 ≤ N.sc.L := Real.one_le_rpow N.sc.one_lt_alt.le N.sc.eps_pos.le
  have hb : 1 ≤ Real.exp N.sc.L := Real.one_le_exp (by linarith)
  have hg0 : Real.exp N.sc.L ≤ N.g 0 := by
    refine le_trans ?_ (s2 0).1
    have hk' : (1 : ℝ) ≤ N.R.k := by exact_mod_cast (by omega : 1 ≤ N.R.k)
    have h1 : Real.exp N.sc.L ≤ (N.R.k : ℝ) * Real.exp N.sc.L := by nlinarith
    exact h1.trans (le_self_pow₀ (hb.trans h1) (by norm_num))
  have hlog := GlobalTheory.ColumnClassLog.log_le_of_count (Nat.card (MulAction.orbitRel.Quotient G' D')) N.R.f n N.Nm (N.g 0) (N.g 1)
    (Pr.T u) N.rd N.sc.L hf1 hn hnN (hP.T_prime u).pos hrd0 hL s1 s4 hg0 (N.g_prime 1).pos (by
      refine ((Nat.cast_le.2 hle).trans hcount).trans ?_
      rw [hrd, hE, mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      rw [pow_two n]
      exact_mod_cast hfib')
  refine (Real.le_exp_log _).trans (Real.exp_le_exp.2 (hlog.trans ?_))
  have hG : 0 ≤ Real.log ((N.g 0 : ℝ) * N.g 1 * Pr.T u) := by
    have : 1 ≤ N.g 0 * N.g 1 * Pr.T u :=
      Nat.mul_pos (Nat.mul_pos (N.g_prime 0).pos (N.g_prime 1).pos) (hP.T_prime u).pos
    exact Real.log_nonneg (by exact_mod_cast this)
  have hm : (1 : ℝ) ≤ (N.R.m : ℝ) ^ 2 := by
    have : (1 : ℝ) ≤ N.R.m := by exact_mod_cast (by have := N.R.two_le_m; omega : 1 ≤ N.R.m)
    exact one_le_pow₀ this
  unfold errUnit
  calc 55 * (N.R.f : ℝ) * (N.Nm : ℝ) ^ 2 * Real.log ((N.g 0 : ℝ) * N.g 1 * Pr.T u)
      = 55 * (N.R.f * 1 * (N.Nm : ℝ) ^ 2 * Real.log ((N.g 0 : ℝ) * N.g 1 * Pr.T u)) := by ring
    _ ≤ _ := by gcongr

theorem classNumbers_le : ∃ C : ℝ, 0 ≤ C ∧ ∀ (D : D7) (N : NumDatum) (X : Fields) (s : Seam D X) (Pr : Primes X) (W : Wts X Pr.Word N.R) (Ch : Chars X Pr N.R.m) (G : ChGlob X N.R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (Sg : Set ℕ) (mu : Tup X.F X.E X.K Sg) (cst : LocCst X (rowSG Pr sel mu)) (I : ChIdx X Pr N.R (QE sel (mu : Chr X.F X.E X.K))) (dl : ℂ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (pl : RPl N.R ≃ X.Tau) (u : Pr.Word) (δ : Code N), Hyp N s W Ch G sel mu cst I dl χ cD pl u δ → (∀ j ≤ N.R.m, ∀ b : I.β j, (Nat.card ((chF W sel mu I u j).mem b).Cl : ℝ) ≤ Real.exp (C * errUnit N (Pr.T u))) ∧ (Nat.card (evGSD W Ch sel mu (rPsymF Ch) u).Cl : ℝ) ≤ Real.exp (C * errUnit N (Pr.T u)) ∧ (topClassNumber Ch sel mu u : ℝ) ≤ Real.exp (C * errUnit N (Pr.T u)) := by
  refine ⟨55, by norm_num, ?_⟩
  intro D N X s Pr W Ch G sel Sg mu cst I dl χ cD pl u δ hyp
  obtain ⟨hH, -, -, -, hmu, -, -, -, hS⟩ := hyp
  have hQ : QE sel (mu : Chr X.F X.E X.K) = ∅ := by
    rw [hmu]
    exact twistPrimes_trivialTuple_empty sel Sg
  have hSG : rowSG Pr sel mu = Pr.vGs := by
    unfold rowSG uSG
    ext w
    classical
    rw [Finset.mem_union, hQ]
    simp
  have hk : 5 ≤ N.R.k := by have := N.R.m_add_three_le_k; have := N.R.two_le_m; omega
  have hm : 2 ≤ N.R.N N.R.m := by unfold Ranks.N; omega
  refine ⟨fun j hj b => ?_, ?_, ?_⟩
  · have hn : 1 ≤ N.R.N j := by unfold Ranks.N; omega
    have hnN : N.R.N j ≤ N.Nm := by unfold NumDatum.Nm Ranks.N; gcongr
    refine @card_orbits_le_exp D N X s Pr hH pl u δ hS _ hn hnN _ _ subset_rfl rfl (FrmG (I.levG j b) (I.levQ j b))
      (ChPt (R := N.R) (Pr := Pr) sel mu u j) _ (frmAct (I.levG j b) (I.levQ j b)) DecoF.deco ?_
      fun g x => ⟨(g, 1, 1), rfl⟩
    intro x y hxy
    refine Subtype.ext (Prod.ext hxy (funext fun P => ?_))
    exact absurd P.2 (Finset.eq_empty_iff_forall_notMem.1 hQ P.1)
  · exact @card_orbits_le_exp D N X s Pr hH pl u δ hS (N.R.N N.R.m - 1) (by omega) (Nat.sub_le _ _) ∅ _ (Finset.empty_subset _) hSG
      (FormG (rowTy Ch sel mu (rPsymF Ch)).inv) (RowPt Pr N.R sel mu) _ (formAct (rowTy Ch sel mu (rPsymF Ch)).inv) id
      Function.injective_id fun g x => ⟨(g, 1), rfl⟩
  · unfold topClassNumber
    exact card_orbits_le_exp (n := N.R.N N.R.m) hH pl u hS (le_trans (by norm_num) hm) le_rfl subset_rfl hSG id Function.injective_id
      fun g x => ⟨⟨(g, 1), Subgroup.mem_prod.2 ⟨Subgroup.mem_top _, one_mem _⟩⟩, rfl⟩

end GlobalTheory.ChainClassNumbers
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermSliceContinuousInvariant
section
open NumberField MeasureTheory GlobalTheory.CuspRep

noncomputable section

namespace GlobalTheory.SliceTwo

open GlobalTheory.LeviGA

theorem setIntegral_comp_contAddEquiv {X : Type} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X]
    [LocallyCompactSpace X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [μ.IsAddHaarMeasure]
    (N : AddSubgroup X) [Countable N] {𝓕 : Set X} (h𝓕 : IsAddFundamentalDomain N 𝓕 μ) (h1 : μ 𝓕 = 1)
    (T : X ≃ₜ+ X) (hT : ∀ n ∈ N, T n ∈ N) (hT' : ∀ n ∈ N, T.symm n ∈ N)
    (f : X → ℂ) (hf : ∀ n ∈ N, ∀ x, f (n + x) = f x) :
    ∫ x in 𝓕, f (T x) ∂μ = ∫ x in 𝓕, f x ∂μ := by
  let m := T.toHomeomorph.toMeasurableEquiv
  haveI : (μ.map m).IsAddHaarMeasure := T.isAddHaarMeasure_map μ
  let e : N ≃ N :=
    { toFun := fun n => ⟨T.symm n, hT' _ n.2⟩
      invFun := fun n => ⟨T n, hT _ n.2⟩
      left_inv := fun n => Subtype.ext (T.apply_symm_apply _)
      right_inv := fun n => Subtype.ext (T.symm_apply_apply _) }
  have hD : IsAddFundamentalDomain N (m '' 𝓕) (μ.map m) :=
    h𝓕.image_of_equiv m.toEquiv (MeasurePreserving.symm m ⟨m.measurable, rfl⟩).quasiMeasurePreserving e
      fun n x => by
        change T (T.symm n + x) = n + T x
        rw [map_add, T.apply_symm_apply]
  have hD2 : IsAddFundamentalDomain N 𝓕 (μ.map m) :=
    h𝓕.mono (Measure.absolutelyContinuous_isAddHaarMeasure _ _)
  have hinv : ∀ (n : N) (x : X), f (n +ᵥ x) = f x := fun n x => hf n n.2 x
  obtain ⟨c, hc⟩ : ∃ c : NNReal, μ.map m = c • μ := ⟨_, Measure.isAddLeftInvariant_eq_smul (μ.map m) μ⟩
  have hm : (μ.map m) (m '' 𝓕) = 1 := by
    rw [m.map_apply, m.preimage_image, h1]
  have hc1 : c = 1 := by
    have h3 := hD.measure_eq hD2
    rw [hm, hc, Measure.smul_apply, h1] at h3
    have h4 : (c : ENNReal) = 1 := by simpa [ENNReal.smul_def] using h3.symm
    exact_mod_cast h4
  have step := m.measurableEmbedding.setIntegral_map (μ := μ) f (m '' 𝓕)
  rw [m.preimage_image] at step
  change ∫ x in 𝓕, f (m x) ∂μ = _
  rw [← step, hD.setIntegral_eq hD2 hinv, hc, hc1, one_smul]

section Shear

variable {R : Type} [CommRing R] {a r : ℕ}

def shear (D : Matrix (Fin a) (Fin a) R) (x : BlockIx a r → R) : BlockIx a r → R :=
  fun p => (nilM x * D) p.1.1 p.1.2

theorem nilM_apply_ix (x : BlockIx a r → R) (p : BlockIx a r) : nilM x p.1.1 p.1.2 = x p := by
  unfold nilM
  rw [Matrix.of_apply, dif_pos p.2]

theorem nilM_injective : Function.Injective (fun x : BlockIx a r → R => nilM x) := by
  intro x y h
  funext p
  have h' := congrFun (congrFun h p.1.1) p.1.2
  simp only at h'
  rwa [nilM_apply_ix, nilM_apply_ix] at h'

theorem nilM_add (x y : BlockIx a r → R) : nilM (x + y) = nilM x + nilM y := by
  ext i j; simp only [nilM, Matrix.of_apply, Matrix.add_apply]; split_ifs <;> simp

theorem shear_add (D : Matrix (Fin a) (Fin a) R) (x y : BlockIx a r → R) :
    shear D (x + y) = shear D x + shear D y := by
  funext p
  simp only [shear, nilM_add, Matrix.add_mul, Matrix.add_apply, Pi.add_apply]

theorem nilM_shear (D : Matrix (Fin a) (Fin a) R) (hD : ∀ i j : Fin a, r ≤ (i : ℕ) → (j : ℕ) < r → D i j = 0)
    (x : BlockIx a r → R) : nilM (shear D x) = nilM x * D := by
  ext i j
  by_cases h : (i : ℕ) < r ∧ r ≤ (j : ℕ)
  · conv_lhs => rw [nilM, Matrix.of_apply, dif_pos h]
    rfl
  · have h0 : nilM (shear D x) i j = 0 := by
      unfold nilM
      rw [Matrix.of_apply, dif_neg h]
    rw [h0, Matrix.mul_apply]
    refine (Finset.sum_eq_zero fun k _ => ?_).symm
    by_cases hk : (i : ℕ) < r ∧ r ≤ (k : ℕ)
    · rw [hD k j hk.2 (by omega), mul_zero]
    · have h1 : nilM x i k = 0 := by
        unfold nilM
        rw [Matrix.of_apply, dif_neg hk]
      rw [h1, zero_mul]

theorem mul_nilM (D : Matrix (Fin a) (Fin a) R)
    (hD1 : ∀ i j : Fin a, (i : ℕ) < r → D i j = (1 : Matrix (Fin a) (Fin a) R) i j)
    (hD : ∀ i j : Fin a, r ≤ (i : ℕ) → (j : ℕ) < r → D i j = 0) (x : BlockIx a r → R) : D * nilM x = nilM x := by
  ext i j
  rw [Matrix.mul_apply]
  by_cases hi : (i : ℕ) < r
  · rw [show (∑ k, D i k * nilM x k j) = ∑ k, (1 : Matrix (Fin a) (Fin a) R) i k * nilM x k j from
      Finset.sum_congr rfl fun k _ => by rw [hD1 i k hi]]
    rw [← Matrix.mul_apply, Matrix.one_mul]
  · have h0 : nilM x i j = 0 := by
      unfold nilM
      rw [Matrix.of_apply, dif_neg (fun h => hi h.1)]
    rw [h0]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hk : (k : ℕ) < r ∧ r ≤ (j : ℕ)
    · rw [hD i k (by omega) hk.1, zero_mul]
    · have h1 : nilM x k j = 0 := by
        unfold nilM
        rw [Matrix.of_apply, dif_neg hk]
      rw [h1, mul_zero]

theorem unip_mul_eq (D : GL (Fin a) R)
    (hD1 : ∀ i j : Fin a, (i : ℕ) < r → (D : Matrix (Fin a) (Fin a) R) i j = (1 : Matrix (Fin a) (Fin a) R) i j)
    (hD : ∀ i j : Fin a, r ≤ (i : ℕ) → (j : ℕ) < r → (D : Matrix (Fin a) (Fin a) R) i j = 0)
    (x : BlockIx a r → R) : unip x * D = D * unip (shear (D : Matrix (Fin a) (Fin a) R) x) := by
  apply Units.ext
  change (1 + nilM x) * (D : Matrix (Fin a) (Fin a) R) =
    (D : Matrix (Fin a) (Fin a) R) * (1 + nilM (shear (D : Matrix (Fin a) (Fin a) R) x))
  rw [nilM_shear _ hD, add_mul, mul_add, one_mul, mul_one, ← mul_assoc, mul_nilM _ hD1 hD]

theorem shear_shear (D D' : Matrix (Fin a) (Fin a) R)
    (hD : ∀ i j : Fin a, r ≤ (i : ℕ) → (j : ℕ) < r → D i j = 0)
    (hD' : ∀ i j : Fin a, r ≤ (i : ℕ) → (j : ℕ) < r → D' i j = 0) (h : D * D' = 1) (x : BlockIx a r → R) :
    shear D' (shear D x) = x := by
  apply nilM_injective
  simp only
  rw [nilM_shear _ hD', nilM_shear _ hD, Matrix.mul_assoc, h, Matrix.mul_one]

theorem continuous_shear [TopologicalSpace R] [IsTopologicalRing R] (D : Matrix (Fin a) (Fin a) R) :
    Continuous (shear (r := r) D) := by
  have hN : Continuous fun x : BlockIx a r → R => nilM x := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    unfold nilM
    simp only [Matrix.of_apply]
    split_ifs
    · exact continuous_apply _
    · exact continuous_const
  have hM : Continuous fun x : BlockIx a r → R => nilM x * D := hN.matrix_mul continuous_const
  exact continuous_pi fun p => (hM.matrix_elem p.1.1 p.1.2)

theorem nilM_map {S : Type} [CommRing S] (f : R →+* S) (x : BlockIx a r → R) :
    nilM (fun p => f (x p)) = (nilM x).map f := by
  ext i j; simp only [nilM, Matrix.of_apply, Matrix.map_apply]; split_ifs <;> simp

theorem shear_map {S : Type} [CommRing S] (f : R →+* S) (D : Matrix (Fin a) (Fin a) R) (x : BlockIx a r → R) :
    shear (D.map f) (fun p => f (x p)) = fun p => f (shear D x p) := by
  funext p
  simp only [shear]
  rw [nilM_map, ← Matrix.map_mul]
  rfl

theorem blkGL_one_top (hr : r ≤ a) (l : GL (Fin (a - r)) R) (i j : Fin a) (hi : (i : ℕ) < r) :
    (blkGL hr (1, l) : Matrix (Fin a) (Fin a) R) i j = (1 : Matrix (Fin a) (Fin a) R) i j := by
  obtain ⟨i, rfl⟩ := (blkEquiv hr).surjective i
  obtain ⟨j, rfl⟩ := (blkEquiv hr).surjective j
  rw [blkGL_apply]
  have e1 : (1 : Matrix (Fin a) (Fin a) R) (blkEquiv hr i) (blkEquiv hr j) =
      (1 : Matrix (Fin r ⊕ Fin (a - r)) (Fin r ⊕ Fin (a - r)) R) i j := by
    simp [Matrix.one_apply, (blkEquiv hr).injective.eq_iff]
  rw [e1]
  rcases i with i | i
  · rcases j with j | j <;> simp [Matrix.one_apply]
  · exfalso
    rw [blkEquiv_inr] at hi
    omega

theorem blkGL_one_low (hr : r ≤ a) (l : GL (Fin (a - r)) R) (i j : Fin a) (hi : r ≤ (i : ℕ)) (hj : (j : ℕ) < r) :
    (blkGL hr (1, l) : Matrix (Fin a) (Fin a) R) i j = 0 := by
  rcases blkGL_block hr (1, l) i j with h | h
  · exact absurd (h.2 hj) (by omega)
  · exact h

end Shear

theorem slice_ratGL_mul : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a r : ℕ) (hr : r ≤ a)
    [MeasurableSpace (BlockIx a r → Ad E)] [BorelSpace (BlockIx a r → Ad E)] (μ : Measure (BlockIx a r → Ad E))
    (𝓕 : Set (BlockIx a r → Ad E)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratN E a r) 𝓕 μ → μ 𝓕 = 1 →
    ∀ φ : GA E a → ℂ, Continuous φ → (∀ γ g, φ (ratGL E a γ * g) = φ g) →
    ∀ (m₁ : GA E r) (t : GL (Fin a) (Af E)) (κ : Kinf E a) (γ : GL (Fin (a - r)) E) (g : GA E (a - r)),
    GlobalTheory.SliceTwo.slice E μ 𝓕 hr φ m₁ t κ (ratGL E (a - r) γ * g) = GlobalTheory.SliceTwo.slice E μ 𝓕 hr φ m₁ t κ g := by
  intro E _ _ _ a r hr _ _ μ 𝓕 hμ h𝓕 h1 φ _ hφ m₁ t κ γ g
  haveI := hμ
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele E
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele E
  haveI : Countable E := Countable.of_equiv _ (Module.finBasis ℚ E).equivFun.toEquiv.symm
  haveI : Countable (ratN E a r) := by
    have : ((ratN E a r : AddSubgroup _) : Set (BlockIx a r → Ad E)) = Set.range
        (AddMonoidHom.compLeft (algebraMap E (Ad E)).toAddMonoidHom (BlockIx a r)) := AddMonoidHom.coe_range _
    change Countable (((ratN E a r : AddSubgroup _) : Set (BlockIx a r → Ad E)))
    rw [this]; exact (Set.countable_range _).to_subtype

  let G : GL (Fin a) E := blkGL hr (1, γ)
  have hDG : ratGL E a G = blkGL hr (1, ratGL E (a - r) γ) :=
    (map_blkGL hr (algebraMap E (Ad E)) (1, γ)).trans (by rw [map_one]; rfl)
  have hDG' : (ratGL E a G)⁻¹ = blkGL hr (1, (ratGL E (a - r) γ)⁻¹) := by
    rw [hDG, ← map_inv, Prod.inv_mk, inv_one]
  let M : Matrix (Fin a) (Fin a) (Ad E) := (ratGL E a G : Matrix (Fin a) (Fin a) (Ad E))
  let M' : Matrix (Fin a) (Fin a) (Ad E) := ((ratGL E a G)⁻¹ : GA E a)
  have hM1 : ∀ i j : Fin a, (i : ℕ) < r → M i j = (1 : Matrix (Fin a) (Fin a) (Ad E)) i j := fun i j hi => by
    change ((ratGL E a G : GA E a) : Matrix (Fin a) (Fin a) (Ad E)) i j = _
    rw [hDG]; exact blkGL_one_top hr _ i j hi
  have hM2 : ∀ i j : Fin a, r ≤ (i : ℕ) → (j : ℕ) < r → M i j = 0 := fun i j hi hj => by
    change ((ratGL E a G : GA E a) : Matrix (Fin a) (Fin a) (Ad E)) i j = _
    rw [hDG]; exact blkGL_one_low hr _ i j hi hj
  have hM2' : ∀ i j : Fin a, r ≤ (i : ℕ) → (j : ℕ) < r → M' i j = 0 := fun i j hi hj => by
    change (((ratGL E a G)⁻¹ : GA E a) : Matrix (Fin a) (Fin a) (Ad E)) i j = _
    rw [hDG']; exact blkGL_one_low hr _ i j hi hj
  have hMM' : M * M' = 1 := Units.mul_inv _
  have hM'M : M' * M = 1 := Units.inv_mul _
  let T : (BlockIx a r → Ad E) ≃ₜ+ (BlockIx a r → Ad E) :=
    { toFun := shear M
      invFun := shear M'
      left_inv := fun x => shear_shear M M' hM2 hM2' hMM' x
      right_inv := fun x => shear_shear M' M hM2' hM2 hM'M x
      map_add' := shear_add M
      continuous_toFun := continuous_shear M
      continuous_invFun := continuous_shear M' }
  have hT : ∀ n ∈ ratN E a r, T n ∈ ratN E a r := by
    rintro _ ⟨e, rfl⟩
    exact ⟨shear (G : Matrix (Fin a) (Fin a) E) e, (shear_map (algebraMap E (Ad E)) _ e).symm⟩
  have hT' : ∀ n ∈ ratN E a r, T.symm n ∈ ratN E a r := by
    rintro _ ⟨e, rfl⟩
    exact ⟨shear ((G⁻¹ : GL (Fin a) E) : Matrix (Fin a) (Fin a) E) e, (shear_map (algebraMap E (Ad E)) _ e).symm⟩

  let B : GA E a := blkGL hr (m₁, g) * finGL E a t * infGL E a (Unitary.toUnits κ)
  let f : (BlockIx a r → Ad E) → ℂ := fun y => φ (unip y * B)
  have hf : ∀ n ∈ ratN E a r, ∀ x, f (n + x) = f x := by
    rintro _ ⟨e, rfl⟩ x
    change φ (unip ((fun p => algebraMap E (Ad E) (e p)) + x) * B) = φ (unip x * B)
    rw [unip_add, unip_algebraMap, mul_assoc, hφ]
  have key : ∀ x, φ (unip x * (blkGL hr (m₁, ratGL E (a - r) γ * g) * finGL E a t * infGL E a (Unitary.toUnits κ))) =
      f (T x) := fun x => by
    rw [show (m₁, ratGL E (a - r) γ * g) = ((1 : GA E r), ratGL E (a - r) γ) * (m₁, g) by simp, map_mul, ← hDG]
    change _ = φ (unip (shear M x) * (blkGL hr (m₁, g) * finGL E a t * infGL E a (Unitary.toUnits κ)))
    simp only [mul_assoc]
    rw [← mul_assoc (unip x) (ratGL E a G), unip_mul_eq (ratGL E a G) hM1 hM2, mul_assoc, hφ]
  unfold slice
  calc ∫ x in 𝓕, φ (unip x * (blkGL hr (m₁, ratGL E (a - r) γ * g) * finGL E a t * infGL E a (Unitary.toUnits κ))) ∂μ
      = ∫ x in 𝓕, f (T x) ∂μ := by congr 1; funext x; exact key x
    _ = ∫ x in 𝓕, f x ∂μ := setIntegral_comp_contAddEquiv μ (ratN E a r) h𝓕 h1 T hT hT' f hf

end GlobalTheory.SliceTwo

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegAddLeDegOfIdealSmulLe
section
open NumberField IsDedekindDomain Formalism.BasicNotions GlobalTheory.AllWt GlobalTheory.FlatLine

noncomputable section

namespace GlobalTheory.TwistIdeal

theorem htMap_le {K V W ι κ : Type} [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] [AddCommGroup V]
    [Module K V] [AddCommGroup W] [Module K W] [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    {b : Module.Basis ι K V} {X : InfinitePlace K → Matrix ι ι ℂ} {b' : Module.Basis κ K W}
    {X' : InfinitePlace K → Matrix κ κ ℂ} {N : (K →+* ℂ) → V → ℝ} {N' : (K →+* ℂ) → W → ℝ}
    (hG : IsGram b X N) (hG' : IsGram b' X' N') (φ : V →ₗ[K] W) (hφ : φ ≠ 0) (t : (K →+* ℂ) → ℝ)
    (ht : ∀ σ, 0 < t σ) (htc : ∀ σ, t ((starRingEnd ℂ).comp σ) = t σ) (hN : ∀ σ x, N' σ (φ x) ≤ t σ * N σ x) :
    Formalism.HN.htMap b X b' X' φ ≤ 2 * (∑ σ : K →+* ℂ, Real.log (t σ)) / (Module.finrank ℚ K : ℝ) := by
  have hop : ∀ v : InfinitePlace K, Formalism.HN.opNormAt b X b' X' v φ ^ 2 ≤ t v.embedding ^ 2 := fun v =>
    opNormAt_sq_le b X b' X' (fun v => (hG v).1) v (IsTotallyComplex.isComplex v) φ _ (sq_nonneg _) fun x => by
      rw [← normAt_sq_eq_majAt, ← normAt_sq_eq_majAt, (hG v).2, (hG' v).2, ← mul_pow]
      exact pow_le_pow_left₀ (normAt_nonneg _ _ _ _ |>.trans_eq ((hG' v).2 _)) (hN _ _) 2
  have hpos : ∀ v : InfinitePlace K, 0 < Formalism.HN.opNormAt b X b' X' v φ := fun v =>
    Formalism.HN.PlaceOperatorNorms.opNormAt_pos b X b' X' (fun v => (hG v).1) (fun v => (hG' v).1) v φ hφ
  have hs : ∑ σ : K →+* ℂ, Real.log (t σ) = 2 * ∑ v : InfinitePlace K, Real.log (t v.embedding) := by
    rw [← GlobalTheory.SlopeExt.sum_mk K fun v => Real.log (t v.embedding)]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rcases InfinitePlace.embedding_mk_eq σ with h | h
    · rw [h]
    · rw [h]
      have e : ComplexEmbedding.conjugate σ = (starRingEnd ℂ).comp σ :=
        RingHom.ext fun x => by simp [ComplexEmbedding.conjugate_coe_eq]
      rw [e, htc σ]
  have hd : (Module.finrank ℚ K : ℝ) = 2 * Formalism.HN.nPl K := by
    have := GlobalTheory.SlopeExt.sum_mk K fun _ => (1 : ℝ)
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, Embeddings.card] at this
    rw [this]; rfl
  have hn : (0 : ℝ) < Formalism.HN.nPl K := by
    have : (0 : ℝ) < Module.finrank ℚ K := Nat.cast_pos.2 Module.finrank_pos
    linarith
  unfold Formalism.HN.htMap
  rw [hs, hd]
  have hsum : ∑ v, Real.log (Formalism.HN.opNormAt b X b' X' v φ ^ 2) ≤ ∑ v : InfinitePlace K, 2 * Real.log (t v.embedding) :=
    Finset.sum_le_sum fun v _ => by
      have := Real.log_le_log (pow_pos (hpos v) 2) (hop v)
      rw [Real.log_pow, Real.log_pow] at this
      rw [Real.log_pow]
      push_cast at this ⊢
      exact this
  rw [← Finset.mul_sum] at hsum
  rw [one_div, inv_mul_le_iff₀ hn]
  have : 2 * (2 * ∑ v : InfinitePlace K, Real.log (t v.embedding)) / (2 * (Formalism.HN.nPl K : ℝ)) * Formalism.HN.nPl K =
      2 * ∑ v : InfinitePlace K, Real.log (t v.embedding) := by
    field_simp
  linarith

end GlobalTheory.TwistIdeal

namespace GlobalTheory.TwistIdeal

theorem deg_add_le_deg_of_ideal_smul_le : ∀ (K V : Type) [Field K] [NumberField K] [IsTotallyComplex K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (W : Type) [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W] (N : (K →+* ℂ) → V → ℝ) (N' : (K →+* ℂ) → W → ℝ) (φ : V →ₗ[K] W) (t : (K →+* ℂ) → ℝ) (L : Submodule (𝓞 K) V) (L' : Submodule (𝓞 K) W) (𝔞 : Ideal (𝓞 K)), HasGram N → HasGram N' → Function.Injective φ → (∀ σ, 0 < t σ) → (∀ σ, t ((starRingEnd ℂ).comp σ) = t σ) → (∀ σ x, N' σ (φ x) ≤ t σ * N σ x) → L.FG → L'.FG → 𝔞 ≠ ⊥ → 𝔞 • L.map (φ.restrictScalars (𝓞 K)) ≤ L' → Formalism.HN.rkK L' = Formalism.HN.rkK L → deg N L + (Formalism.HN.rkK L : ℝ) * (-((∑ σ : K →+* ℂ, Real.log (t σ)) / (Module.finrank ℚ K : ℝ)) - Real.log (Ideal.absNorm 𝔞 : ℝ) / (Module.finrank ℚ K : ℝ)) ≤ deg N' L' := by
  intro K V _ _ _ _ _ _ _ W _ _ _ _ N N' φ t L L' 𝔞 hN hN' hinj htpos htc hNb hL hL' h𝔞 hsub hrk
  by_cases h0 : L = ⊥
  · subst h0
    have h1 : Formalism.HN.rkK (⊥ : Submodule (𝓞 K) V) = 0 := by simp [Formalism.HN.rkK]
    rw [h1] at hrk
    simp [deg, h1, hrk]
  obtain ⟨⟨n, ⟨b, X⟩, hG⟩⟩ := hN
  obtain ⟨⟨n', ⟨b', X'⟩, hG'⟩⟩ := hN'
  letI : StarRing K := starRingOfComm
  have hI : ((𝔞 : FractionalIdeal (nonZeroDivisors (𝓞 K)) K)) ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.2 h𝔞
  have hsm : Formalism.HermitianLatticesTheory.idealSmul (((𝔞 : FractionalIdeal (nonZeroDivisors (𝓞 K)) K)) : Submodule (𝓞 K) K)
      (L.map (φ.restrictScalars (𝓞 K))) ≤ L' := by
    refine Submodule.span_le.2 ?_
    rintro z ⟨a, ha, x, hx, rfl⟩
    obtain ⟨r, hr, rfl⟩ := (FractionalIdeal.mem_coeIdeal (S := (nonZeroDivisors (𝓞 K))) (P := K)).1 ha
    rw [algebraMap_smul]
    exact hsub (Submodule.smul_mem_smul hr hx)
  have key := Formalism.ExtensionFiltration.twistLower K V (Fin n) W (Fin n') b X b' X' (fun v => (hG v).1) (fun v => (hG' v).1)
    φ L L' (𝔞 : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) hI hL hL' h0 hinj hsm hrk
  have hφ : φ ≠ 0 := by
    intro h
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h0
    exact hx0 (hinj (by rw [h, map_zero, LinearMap.zero_apply]))
  have hht := htMap_le hG hG' φ hφ t htpos htc hNb
  rw [FractionalIdeal.coeIdeal_absNorm] at key
  have hb : slope_sq N L / 2 - (∑ σ : K →+* ℂ, Real.log (t σ)) / (Module.finrank ℚ K : ℝ) -
      Real.log (Ideal.absNorm 𝔞 : ℝ) / (Module.finrank ℚ K : ℝ) ≤ slope_sq N' L' / 2 := by
    rw [slope_sq_eq hG hL, slope_sq_eq hG' hL']
    have e1 : 2 * (∑ σ : K →+* ℂ, Real.log (t σ)) / (Module.finrank ℚ K : ℝ) =
        2 * ((∑ σ : K →+* ℂ, Real.log (t σ)) / (Module.finrank ℚ K : ℝ)) := by ring
    have e2 : 2 * Real.log ((Ideal.absNorm 𝔞 : ℚ) : ℝ) / (Module.finrank ℚ K : ℝ) =
        2 * (Real.log (Ideal.absNorm 𝔞 : ℝ) / (Module.finrank ℚ K : ℝ)) := by push_cast; ring
    rw [e1] at hht
    rw [e2] at key
    linarith
  have hr : (0 : ℝ) ≤ Formalism.HN.rkK L := Nat.cast_nonneg _
  unfold deg GlobalTheory.AllWt.slope
  rw [hrk]
  nlinarith [mul_le_mul_of_nonneg_left hb hr]

end GlobalTheory.TwistIdeal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalUnitNormVectorIsotropicHermitianStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published GlobalTheory.PlaneNorm
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_local_unitNorm_vector_isotropic_hermitian : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (K : Type) [Field K] [Algebra F K] (M : ℕ) (J : Matrix (Fin M) (Fin M) E), 2 ≤ M → IsHermND σ J → (∃ u : Fin M → K ⊗[F] E, u ≠ 0 ∧ hR K σ J u u = 0) → ∀ x y : Fin M → E, hE σ J x x ≠ 0 → hE σ J y y ≠ 0 → ∃ w : Fin M → K ⊗[F] E, IsUnitNorm K σ (-(gram2R K σ J (fun i => inclR K (x i)) w)) ∧ IsUnitNorm K σ (-(gram2R K σ J w (fun i => inclR K (y i)))) := by
  first | exact @GlobalTheory.PlaneNorm.exists_local_unitNorm_vector | exact GlobalTheory.PlaneNorm.exists_local_unitNorm_vector | (intros; apply GlobalTheory.PlaneNorm.exists_local_unitNorm_vector <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNilDualFrobeniusStatement
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isNil_dual_frobenius_alt : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (μ' : Fin d → MvPowerSeries (Fin d ⊕ Fin d) F.B), IsLift F.θ μ' → (∀ i, map F.θ (μ' i) = c.μ i) → ∀ (k : ℕ) (e : Fin d ⊕ Fin k → MvPowerSeries (Fin d) F.Q), IsBasis μ' e → IsAdapted F.θ μ' e → IsConn G.dual → ∀ U : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) F.B, IsUnit U → (∀ i, In (⊤ : Ideal F.B) (frob p F.s (e i) - comb (fun l => (U * blk d k (p : F.B) 1) l i) e) ∧ ∀ i', i = Sum.inl i' → In (Ideal.span {(p : F.B)}) (frob p F.s (e i) - comb (fun l => (U * blk d k (p : F.B) 1) l i) e)) → IsNil F.θ F.σ (U.transpose⁻¹ * blk d k 1 (p : F.B)) := by
  first | exact @GlobalTheory.DualFrobNil.isNil_dual_frobenius | exact GlobalTheory.DualFrobNil.isNil_dual_frobenius | (intros; apply GlobalTheory.DualFrobNil.isNil_dual_frobenius <;> assumption)
end

