import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.LevelChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3167
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3166

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PInvMin
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

private theorem aeval_inv_reverse_eq_zero_iff {K A : Type} [Field K] [Ring A] [Algebra K A] (u : Aˣ) (f : K[X]) :
    Polynomial.aeval (↑u⁻¹ : A) f.reverse = 0 ↔ Polynomial.aeval (u : A) f = 0 := by
  let S : Subalgebra K A := Algebra.adjoin K {(u : A), ↑u⁻¹}
  letI : CommRing S := Algebra.adjoinCommRingOfComm K (by
    intro a ha b hb
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp)
  let x : S := ⟨u, Algebra.subset_adjoin (by simp)⟩
  let y : S := ⟨↑u⁻¹, Algebra.subset_adjoin (by simp)⟩
  letI : Invertible x := ⟨y, Subtype.ext (by simp [x, y]), Subtype.ext (by simp [x, y])⟩
  have key := Polynomial.eval₂_reverse_eq_zero_iff (algebraMap K S) x f
  have h1 : Polynomial.aeval (↑u⁻¹ : A) f.reverse = S.val (Polynomial.aeval y f.reverse) :=
    Polynomial.aeval_algHom_apply S.val y f.reverse
  have h2 : Polynomial.aeval (u : A) f = S.val (Polynomial.aeval x f) :=
    Polynomial.aeval_algHom_apply S.val x f
  rw [h1, h2, map_eq_zero_iff S.val Subtype.val_injective, map_eq_zero_iff S.val Subtype.val_injective,
    Polynomial.aeval_def, Polynomial.aeval_def]
  exact key

private theorem squarefree_mirror {F : Type} [Field F] (f : F[X]) (h : Squarefree f) :
    Squarefree f.mirror := by
  intro r hr
  obtain ⟨s, hs⟩ := hr
  have hf : f = r.mirror * r.mirror * s.mirror := by
    rw [← Polynomial.mirror_mul_of_domain, ← Polynomial.mirror_mul_of_domain, ← hs,
      Polynomial.mirror_mirror]
  have hu : IsUnit r.mirror := h _ ⟨_, hf⟩
  have hr0 : r ≠ 0 := by
    rintro rfl
    rw [Polynomial.mirror_zero] at hu
    exact not_isUnit_zero hu
  rw [Polynomial.isUnit_iff_degree_eq_zero] at hu ⊢
  rw [Polynomial.degree_eq_natDegree hr0]
  rw [Polynomial.degree_eq_natDegree (Polynomial.mirror_eq_zero.not.mpr hr0),
    Polynomial.mirror_natDegree] at hu
  exact hu

private theorem separable_reverse_of_coeff_zero_ne_zero {K : Type} [Field K] (f : K[X]) (h0 : f.coeff 0 ≠ 0)
    (hs : f.Separable) : f.reverse.Separable := by
  rw [← Polynomial.separable_map (algebraMap K (AlgebraicClosure K))]
  have hm : (f.reverse).map (algebraMap K (AlgebraicClosure K)) =
      (f.map (algebraMap K (AlgebraicClosure K))).mirror := by
    have htd : (f.map (algebraMap K (AlgebraicClosure K))).natTrailingDegree = 0 :=
      Polynomial.natTrailingDegree_eq_zero.mpr
        (Or.inr (by rw [Polynomial.coeff_map]; exact (_root_.map_ne_zero _).mpr h0))
    rw [Polynomial.mirror, htd, pow_zero, _root_.mul_one]
    simp only [Polynomial.reverse, Polynomial.natDegree_map, Polynomial.reflect_map]
  rw [hm, PerfectField.separable_iff_squarefree]
  exact squarefree_mirror _ ((Polynomial.separable_map _).mpr hs).squarefree

theorem UpperTheory.Gal.W2.invMin_of :
    UpperTheory.Gal.W2.InvMin := by
  intro K A _ _ _ _ _ u
  have hint : ∀ v : Aˣ, IsIntegral K (v : A) := fun v => .of_finite K _
  have hc : ∀ v : Aˣ, (minpoly K (v : A)).coeff 0 ≠ 0 := by
    intro v h0
    obtain ⟨q, hq⟩ := Polynomial.X_dvd_iff.mpr h0
    have hne := minpoly.ne_zero (hint v)
    have hq0 : q ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hq
      exact hne hq
    have hev : Polynomial.aeval (v : A) q = 0 := by
      have := minpoly.aeval K (v : A)
      rw [hq, map_mul, Polynomial.aeval_X] at this
      simpa using congrArg (fun z => (↑v⁻¹ : A) * z) this
    have hdeg := minpoly.degree_le_of_ne_zero K (v : A) hq0 hev
    have h2 := Polynomial.natDegree_le_natDegree hdeg
    rw [hq, Polynomial.natDegree_X_mul hq0] at h2
    omega
  set p := minpoly K (u : A) with hp
  have htd : p.natTrailingDegree = 0 := Polynomial.natTrailingDegree_eq_zero.mpr (Or.inr (hc u))
  have hdegrev : p.reverse.natDegree = p.natDegree := by
    rw [Polynomial.reverse_natDegree, htd, Nat.sub_zero]
  have hinvMonic : (invPoly p).Monic := by
    show (Polynomial.C (p.coeff 0)⁻¹ * p.reverse).leadingCoeff = 1
    rw [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C, Polynomial.reverse_leadingCoeff,
      Polynomial.trailingCoeff_eq_coeff_zero (hc u), inv_mul_cancel₀ (hc u)]
  have hinvDeg : (invPoly p).natDegree = p.natDegree := by
    show (Polynomial.C (p.coeff 0)⁻¹ * p.reverse).natDegree = _
    rw [Polynomial.natDegree_C_mul (inv_ne_zero (hc u)), hdegrev]
  have hinvEval : Polynomial.aeval (↑u⁻¹ : A) (invPoly p) = 0 := by
    show Polynomial.aeval (↑u⁻¹ : A) (Polynomial.C (p.coeff 0)⁻¹ * p.reverse) = 0
    rw [map_mul, (aeval_inv_reverse_eq_zero_iff u p).mpr (minpoly.aeval K _), mul_zero]
  have heq : minpoly K (↑u⁻¹ : A) = invPoly p := by
    refine (minpoly.unique K _ hinvMonic hinvEval ?_).symm
    intro q hqm hqe
    have hq0 : q ≠ 0 := hqm.ne_zero
    have h1 : Polynomial.aeval (u : A) q.reverse = 0 := by
      have := (aeval_inv_reverse_eq_zero_iff u⁻¹ q).mpr hqe
      simpa using this
    have h2 := minpoly.degree_le_of_ne_zero K (u : A) (mt Polynomial.reverse_eq_zero.mp hq0) h1
    have h3 := Polynomial.natDegree_le_natDegree h2
    have h4 := Polynomial.reverse_natDegree_le q
    rw [Polynomial.degree_eq_natDegree hinvMonic.ne_zero, Polynomial.degree_eq_natDegree hq0, hinvDeg]
    exact_mod_cast h3.trans h4
  refine ⟨heq, by rw [heq, hinvDeg], fun hs => ?_⟩
  rw [heq]
  have hrev : p.reverse.Separable := separable_reverse_of_coeff_zero_ne_zero p (hc u) hs
  refine hrev.of_dvd ⟨Polynomial.C (p.coeff 0), ?_⟩
  show p.reverse = Polynomial.C (p.coeff 0)⁻¹ * p.reverse * Polynomial.C (p.coeff 0)
  rw [_root_.mul_comm, ← _root_.mul_assoc, ← Polynomial.C_mul, mul_inv_cancel₀ (hc u),
    Polynomial.C_1, _root_.one_mul]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PIsogForm
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

private theorem herm_add_right {g : ℕ} (M : Matrix (Fin g) (Fin g) ℂ) (x a b : Fin g → ℂ) :
    hermForm M x (a + b) = hermForm M x a + hermForm M x b := by
  simp [hermForm, Matrix.mulVec_add, dotProduct_add]

private theorem herm_add_left {g : ℕ} (M : Matrix (Fin g) (Fin g) ℂ) (a b y : Fin g → ℂ) :
    hermForm M (a + b) y = hermForm M a y + hermForm M b y := by
  simp [hermForm, add_dotProduct]

private theorem herm_smul_right {g : ℕ} (M : Matrix (Fin g) (Fin g) ℂ) (c : ℂ) (x a : Fin g → ℂ) :
    hermForm M x (c • a) = star c * hermForm M x a := by
  simp [hermForm, star_smul, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

private theorem herm_smul_left {g : ℕ} (M : Matrix (Fin g) (Fin g) ℂ) (c : ℂ) (a y : Fin g → ℂ) :
    hermForm M (c • a) y = c * hermForm M a y := by
  simp only [hermForm, smul_dotProduct, smul_eq_mul]

private theorem herm_sub_smul {g : ℕ} (H₁ H₂ : Matrix (Fin g) (Fin g) ℂ) (t : ℂ) (x y : Fin g → ℂ) :
    hermForm (H₁ - t • H₂) x y = hermForm H₁ x y - t * hermForm H₂ x y := by
  simp [hermForm, Matrix.sub_mulVec, Matrix.smul_mulVec, dotProduct_sub, dotProduct_smul]

private theorem real_smul_eq {g : ℕ} (c : ℝ) (a : Fin g → ℂ) : c • a = (c : ℂ) • a := by
  ext i; simp

private theorem herm_im_zero {g : ℕ} (M : Matrix (Fin g) (Fin g) ℂ) (s : Set (Fin g → ℂ))
    (hs : Submodule.span ℝ s = ⊤) (h : ∀ x ∈ s, ∀ y ∈ s, (hermForm M x y).im = 0) (z w : Fin g → ℂ) :
    (hermForm M z w).im = 0 := by
  have key : ∀ w ∈ s, ∀ z, (hermForm M z w).im = 0 := by
    intro w hw z
    have hz : z ∈ Submodule.span ℝ s := by rw [hs]; trivial
    induction hz using Submodule.span_induction with
    | mem x hx => exact h x hx w hw
    | zero => simp [hermForm]
    | add a b _ _ ha hb => rw [herm_add_left]; simp [ha, hb]
    | smul c a _ ha => rw [real_smul_eq, herm_smul_left]; simp [ha]
  have hw : w ∈ Submodule.span ℝ s := by rw [hs]; trivial
  induction hw using Submodule.span_induction with
  | mem y hy => exact key y hy z
  | zero => simp [hermForm]
  | add a b _ _ ha hb => rw [herm_add_right]; simp [ha, hb]
  | smul c a _ ha => rw [real_smul_eq, herm_smul_right]; simp [ha]

private theorem bil_dvd {M : Type} [AddCommGroup M] (Bf : LinearMap.BilinForm ℤ M) (n : ℕ) (x y e e' : M) :
    (n : ℤ) ∣ Bf (x + n • e) (y + n • e') - Bf x y := by
  refine ⟨Bf x e' + Bf e y + n * Bf e e', ?_⟩
  simp [map_add, map_nsmul, LinearMap.add_apply, nsmul_eq_mul]
  ring

private theorem form_step {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} (L : Link D G) (h : G.GAf) (n : ℕ)
    {a a' b b' : D.La} {w w' : AfP p ⊗[ℚ] VQ D} (hw : w ∈ LaHat D) (hw' : w' ∈ LaHat D)
    (e : L.actG h (inAf D a) = inAf D b + n • w) (e' : L.actG h (inAf D a') = inAf D b' + n • w') :
    ∃ i : AfP p, IsIntAf i ∧ ((D.EF b b' : ℤ) : AfP p) =
      ((uSimR (AfP p) h : (AfP p)ˣ) : AfP p) * ((D.EF a a' : ℤ) : AfP p) + (n : AfP p) * i := by
  have h1 := MultScale.EFA_actG L h (inAf D a) (inAf D a')
  rw [e, e', MultScale.EFA_inAf] at h1
  simp only [map_add, map_nsmul, LinearMap.add_apply, LinearMap.smul_apply, nsmul_eq_mul,
    MultScale.EFA_inAf] at h1
  have hn : IsIntAf (n : AfP p) := by
    have := MultScale.isIntAf_intCast (p := p) (n : ℤ)
    simpa using this
  refine ⟨-(MultScale.EFA D (inAf D b) w' + MultScale.EFA D w (inAf D b') +
    (n : AfP p) * MultScale.EFA D w w'), ?_, ?_⟩
  · exact MultScale.isIntAf_neg (MultScale.isIntAf_add (MultScale.isIntAf_add
      (MultScale.isIntAf_EFA D (MultScale.inAf_mem D b) hw')
      (MultScale.isIntAf_EFA D hw (MultScale.inAf_mem D b')))
      (MultScale.isIntAf_mul hn (MultScale.isIntAf_EFA D hw hw')))
  · linear_combination h1

private theorem cross_dvd {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} (L : Link D G) (h : G.GAf)
    {D' D'' : PLat D.O D.inv} (inc : D'.La →ₗ[D.O] D''.La) {f : ℕ → D.La →+ D'.La} {nu : ℕ → ℤ}
    {f'' : ℕ → D.La →+ D''.La} {nu'' : ℕ → ℤ} (hf : IsWit D' f nu) (hf'' : IsWit D'' f'' nu'')
    (hyp : ∀ n : ℕ, 0 < n → n.Coprime p → ∀ a b : D.La,
      (∃ u, inc (f n a) = f'' n b + n • u) ↔ ∃ w ∈ LaHat D, L.actG h (inAf D a) = inAf D b + n • w)
    (u₁ u₂ u₃ u₄ : D'.La) (n : ℕ) (hn : 0 < n) (hc : n.Coprime p) :
    (n : ℤ) ∣ D''.EF (inc u₁) (inc u₂) * D'.EF u₃ u₄ - D''.EF (inc u₃) (inc u₄) * D'.EF u₁ u₂ := by
  unfold IsWit at hf hf''
  have hX : ∀ x x' : D'.La, ∃ b b' a a' : D.La,
      (D''.EF (inc x) (inc x') ≡ nu'' n * (2 * D.EF b b') [ZMOD n]) ∧
      (D'.EF x x' ≡ nu n * (2 * D.EF a a') [ZMOD n]) ∧
      ∃ i : AfP p, IsIntAf i ∧ ((D.EF b b' : ℤ) : AfP p) =
        ((uSimR (AfP p) h : (AfP p)ˣ) : AfP p) * ((D.EF a a' : ℤ) : AfP p) + (n : AfP p) * i := by
    intro x x'
    obtain ⟨a, e, rfl⟩ := (hf.2 n hn hc).2.2.2.1 x
    obtain ⟨a', e', rfl⟩ := (hf.2 n hn hc).2.2.2.1 x'
    obtain ⟨b, E, hb⟩ := (hf''.2 n hn hc).2.2.2.1 (inc (f n a))
    obtain ⟨b', E', hb'⟩ := (hf''.2 n hn hc).2.2.2.1 (inc (f n a'))
    obtain ⟨w, hw, hwe⟩ := (hyp n hn hc a b).1 ⟨E, hb⟩
    obtain ⟨w', hw', hwe'⟩ := (hyp n hn hc a' b').1 ⟨E', hb'⟩
    refine ⟨b, b', a, a', ?_, ?_, form_step L h n hw hw' hwe hwe'⟩
    · have h1 : inc (f n a + n • e) = f'' n b + n • (E + inc e) := by
        rw [map_add, map_nsmul, hb, smul_add, add_assoc]
      have h2 : inc (f n a' + n • e') = f'' n b' + n • (E' + inc e') := by
        rw [map_add, map_nsmul, hb', smul_add, add_assoc]
      rw [h1, h2]
      exact (Int.modEq_iff_dvd.mpr (bil_dvd D''.EF n _ _ _ _)).symm.trans
        (Int.modEq_iff_dvd.mpr ((hf''.2 n hn hc).2.2.2.2 b b')).symm
    · exact (Int.modEq_iff_dvd.mpr (bil_dvd D'.EF n _ _ _ _)).symm.trans
        (Int.modEq_iff_dvd.mpr ((hf.2 n hn hc).2.2.2.2 a a')).symm
  obtain ⟨b1, b2, a1, a2, hX1, hY1, i12, hi12, he12⟩ := hX u₁ u₂
  obtain ⟨b3, b4, a3, a4, hX3, hY3, i34, hi34, he34⟩ := hX u₃ u₄
  have hZ : (n : ℤ) ∣ D.EF b1 b2 * D.EF a3 a4 - D.EF b3 b4 * D.EF a1 a2 := by
    apply IntDvd.int_dvd_of_eq_mul_isIntAf p n hn hc _
      (i12 * ((D.EF a3 a4 : ℤ) : AfP p) - i34 * ((D.EF a1 a2 : ℤ) : AfP p))
    · rw [sub_eq_add_neg]
      exact MultScale.isIntAf_add (MultScale.isIntAf_mul hi12 (MultScale.isIntAf_intCast _))
        (MultScale.isIntAf_neg (MultScale.isIntAf_mul hi34 (MultScale.isIntAf_intCast _)))
    · rw [map_intCast]
      push_cast
      linear_combination ((D.EF a3 a4 : ℤ) : AfP p) * he12 - ((D.EF a1 a2 : ℤ) : AfP p) * he34
  have h0 : nu'' n * (2 * D.EF b1 b2) * (nu n * (2 * D.EF a3 a4)) -
      nu'' n * (2 * D.EF b3 b4) * (nu n * (2 * D.EF a1 a2)) ≡ 0 [ZMOD n] := by
    apply Int.modEq_zero_iff_dvd.mpr
    obtain ⟨k, hk⟩ := hZ
    exact ⟨4 * nu'' n * nu n * k, by linear_combination (4 * nu'' n * nu n) * hk⟩
  exact Int.modEq_zero_iff_dvd.mp (((hX1.mul hY3).sub (hX3.mul hY1)).trans h0)

private theorem cross {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} (L : Link D G) (h : G.GAf)
    {D' D'' : PLat D.O D.inv} (inc : D'.La →ₗ[D.O] D''.La) {f : ℕ → D.La →+ D'.La} {nu : ℕ → ℤ}
    {f'' : ℕ → D.La →+ D''.La} {nu'' : ℕ → ℤ} (hf : IsWit D' f nu) (hf'' : IsWit D'' f'' nu'')
    (hyp : ∀ n : ℕ, 0 < n → n.Coprime p → ∀ a b : D.La,
      (∃ u, inc (f n a) = f'' n b + n • u) ↔ ∃ w ∈ LaHat D, L.actG h (inAf D a) = inAf D b + n • w)
    (u₁ u₂ u₃ u₄ : D'.La) :
    D''.EF (inc u₁) (inc u₂) * D'.EF u₃ u₄ = D''.EF (inc u₃) (inc u₄) * D'.EF u₁ u₂ := by
  set d := D''.EF (inc u₁) (inc u₂) * D'.EF u₃ u₄ - D''.EF (inc u₃) (inc u₄) * D'.EF u₁ u₂ with hd
  suffices hz : d = 0 by exact sub_eq_zero.mp hz
  have hn : 0 < p * d.natAbs + 1 := Nat.succ_pos _
  have hc : (p * d.natAbs + 1).Coprime p :=
    ((Nat.coprime_mul_left_add_right p 1 d.natAbs).mpr (Nat.coprime_one_right p)).symm
  have hdvd := cross_dvd L h inc hf hf'' hyp u₁ u₂ u₃ u₄ _ hn hc
  apply Int.eq_zero_of_abs_lt_dvd hdvd
  have hp : (2 : ℤ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).two_le
  rw [Int.abs_eq_natAbs]
  push_cast
  nlinarith [Int.natCast_nonneg d.natAbs]

theorem UpperTheory.Gal.W2.isogForm_of :
    UpperTheory.Gal.W2.RdForm → UpperTheory.Gal.W2.IsogForm := by
  intro _ p _ D G L h ρ D' D'' P P'' inc hP hP'' hPinc f nu f'' nu'' hf hf'' hyp
  by_cases hall : ∀ u u' : D'.La, D'.EF u u' = 0
  · refine ⟨1, one_pos, fun u u' => ?_⟩
    have h0 : ∀ x : D'.La, x = 0 := fun x => D'.nondeg x (hall x)
    rw [h0 u]
    simp
  push_neg at hall
  obtain ⟨u₃, u₄, hne⟩ := hall
  have hrel : ∀ u u' : D'.La, ((D''.EF (inc u) (inc u') : ℤ) : ℚ) =
      ((D''.EF (inc u₃) (inc u₄) : ℚ) / (D'.EF u₃ u₄ : ℚ)) * (D'.EF u u' : ℚ) := by
    intro u u'
    have hcq : ((D'.EF u₃ u₄ : ℤ) : ℚ) ≠ 0 := by exact_mod_cast hne
    rw [div_mul_eq_mul_div, eq_div_iff hcq]
    exact_mod_cast cross L h inc hf hf'' hyp u u' u₃ u₄
  refine ⟨(D''.EF (inc u₃) (inc u₄) : ℚ) / (D'.EF u₃ u₄ : ℚ), ?_, hrel⟩
  unfold PELU.IsPeriod at hP hP''
  obtain ⟨-, hPinj, -, hspan, H1, -, hpos1, him1⟩ := hP
  obtain ⟨-, -, -, -, H2, -, hpos2, him2⟩ := hP''
  set q : ℚ := (D''.EF (inc u₃) (inc u₄) : ℚ) / (D'.EF u₃ u₄ : ℚ) with hq
  have hzero : ∀ z w, (hermForm (H2 - ((q : ℝ) : ℂ) • H1) z w).im = 0 := by
    apply herm_im_zero _ (Set.range P) hspan
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    rw [herm_sub_smul, Complex.sub_im, Complex.im_ofReal_mul, him1, ← hPinc x, ← hPinc y, him2]
    have hr : ((D''.EF (inc x) (inc y) : ℤ) : ℝ) = (q : ℝ) * ((D'.EF x y : ℤ) : ℝ) := by
      have := congrArg (fun t : ℚ => (t : ℝ)) (hrel x y)
      simpa [hq] using this
    rw [hr]
    ring
  have hM : ∀ z w, hermForm (H2 - ((q : ℝ) : ℂ) • H1) z w = 0 := by
    intro z w
    apply Complex.ext
    · have := hzero (Complex.I • z) w
      rw [herm_smul_left] at this
      simpa using this
    · simpa using hzero z w
  have hu3 : P u₃ ≠ 0 := by
    intro h0
    have hu : u₃ = 0 := hPinj (by rw [h0, map_zero])
    apply hne
    rw [hu]
    simp
  have e := hM (P u₃) (P u₃)
  rw [herm_sub_smul, sub_eq_zero] at e
  have p1 := hpos1 _ hu3
  have p2 := hpos2 _ hu3
  rw [e, Complex.re_ofReal_mul] at p2
  have hpos : (0 : ℝ) < (q : ℝ) := lt_of_not_ge (fun hle => by nlinarith)
  exact Rat.cast_pos.mp hpos
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PLatForm
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

private theorem nsmul_canc {V : Type} [AddCommGroup V] [Module ℚ V] {a : ℕ} (ha : a ≠ 0) {x y : V}
    (h : a • x = a • y) : x = y := by
  have ha' : (a : ℚ) ≠ 0 := by exact_mod_cast ha
  have h' : (a : ℚ) • x = (a : ℚ) • y := by
    rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]; exact h
  exact (smul_right_injective V ha') h'

private theorem ext_lin {Λ V V' : Type} [AddCommGroup Λ] [AddCommGroup V] [AddCommGroup V'] [Module ℚ V]
    [Module ℚ V'] (j : Λ →+ V) (hj : Function.Injective j)
    (hs : ∀ v, ∃ (m : ℕ) (u : Λ), m ≠ 0 ∧ m • v = j u) (f : Λ →+ V') :
    ∃ A : V →ₗ[ℚ] V', ∀ u, A (j u) = f u := by
  choose m u hm hu using hs
  let g : V → V' := fun v => ((m v : ℚ))⁻¹ • f (u v)
  have hg : ∀ v, m v • g v = f (u v) := by
    intro v
    have h0 : (m v : ℚ) ≠ 0 := by exact_mod_cast hm v
    rw [← Nat.cast_smul_eq_nsmul ℚ, smul_smul, mul_inv_cancel₀ h0, one_smul]
  have key : ∀ (a : ℕ) (x : Λ) (v : V), a ≠ 0 → a • v = j x → a • g v = f x := by
    intro a x v ha hx
    have e : m v • x = a • u v := by
      apply hj
      rw [map_nsmul, map_nsmul, ← hx, ← hu v, smul_comm]
    apply nsmul_canc (hm v)
    rw [smul_comm, hg, ← map_nsmul, ← map_nsmul, e]
  have hadd : ∀ v₁ v₂, g (v₁ + v₂) = g v₁ + g v₂ := by
    intro v₁ v₂
    have h12 : m v₁ * m v₂ ≠ 0 := mul_ne_zero (hm _) (hm _)
    apply nsmul_canc h12
    rw [key (m v₁ * m v₂) (m v₂ • u v₁ + m v₁ • u v₂) (v₁ + v₂) h12 ?_]
    · rw [map_add, map_nsmul, map_nsmul, smul_add, ← hg v₁, ← hg v₂, smul_smul, smul_smul, mul_comm (m v₂),
        mul_comm (m v₁) (m v₂)]
    · rw [map_add, map_nsmul, map_nsmul, ← hu v₁, ← hu v₂, smul_add, smul_smul, smul_smul, mul_comm (m v₂)]
  refine ⟨(AddMonoidHom.mk' g hadd).toRatLinearMap, fun x => ?_⟩
  show g (j x) = f x
  have h1 : (1 : ℕ) • g (j x) = f x := key 1 x (j x) one_ne_zero (one_nsmul _)
  simpa using h1

theorem UpperTheory.Gal.W2.latForm_of :
    UpperTheory.Gal.W2.LatForm := by
  intro p _ D G L β β' D' D'' j j'' hP hP'' w m hm hw
  obtain ⟨hj, hjO, hjs, s₀, hs₀, hjF⟩ := hP
  obtain ⟨hj2, hjO2, hjs2, s₂, hs₂, hjF2⟩ := hP''
  obtain ⟨A, hA⟩ := ext_lin j'' hj2 hjs2 (j.comp w.toAddMonoidHom)
  replace hA : ∀ u, A (j'' u) = j (w u) := hA
  haveI := D.finLa
  have hm0 : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  have hAinj : Function.Injective A := by
    refine (injective_iff_map_eq_zero A).2 fun v hv => ?_
    obtain ⟨a, u, ha, hu⟩ := hjs2 v
    have h1 : j (w u) = 0 := by rw [← hA, ← hu, map_nsmul, hv, smul_zero]
    have h2 : w u = 0 := hj (by rw [h1, map_zero])
    have h3 : u = 0 := by
      refine D''.nondeg u fun u' => ?_
      have := hw u u'
      rw [h2] at this
      simp only [map_zero, LinearMap.zero_apply] at this
      rcases mul_eq_zero.1 this.symm with h | h
      · exact absurd h hm.ne'
      · exact h
    apply nsmul_canc ha
    rw [hu, h3, map_zero, smul_zero]
  let Ae := LinearEquiv.ofInjectiveEndo A hAinj
  let B : Module.End ℚ (VQ D) := (Ae.symm : VQ D →ₗ[ℚ] VQ D)
  have hAB : A * B = 1 := LinearEquiv.ofInjectiveEndo_right_inv A hAinj
  have hBA : B * A = 1 := LinearEquiv.ofInjectiveEndo_left_inv A hAinj
  have hcomm : ∀ b, A * actQ D b = actQ D b * A := by
    intro b
    refine LinearMap.ext fun v => ?_
    obtain ⟨a, u, ha, hu⟩ := hjs2 v
    apply nsmul_canc ha
    show a • A (actQ D b v) = a • actQ D b (A v)
    calc a • A (actQ D b v) = A (actQ D b (a • v)) := by rw [map_nsmul, map_nsmul]
      _ = A (j'' (b • u)) := by rw [hu, hjO2]
      _ = j (w (b • u)) := hA _
      _ = j (b • w u) := by rw [map_smul]
      _ = actQ D b (j (w u)) := hjO _ _
      _ = actQ D b (A (a • v)) := by rw [hu, hA]
      _ = a • actQ D b (A v) := by rw [map_nsmul, map_nsmul]
  have hBcomm : ∀ b, B * actQ D b = actQ D b * B := by
    intro b
    calc B * actQ D b = B * actQ D b * (A * B) := by rw [hAB, _root_.mul_one]
      _ = B * (actQ D b * A) * B := by simp only [_root_.mul_assoc]
      _ = B * (A * actQ D b) * B := by rw [hcomm]
      _ = (B * A) * actQ D b * B := by simp only [_root_.mul_assoc]
      _ = actQ D b * B := by rw [hBA, _root_.one_mul]
  obtain ⟨x, hx⟩ := (L.rep_range A).2 hcomm
  obtain ⟨x', hx'⟩ := (L.rep_range B).2 hBcomm
  have hxx' : x * x' = 1 := L.rep_inj (by rw [map_mul, hx, hx', hAB, map_one])
  have hx'x : x' * x = 1 := L.rep_inj (by rw [map_mul, hx, hx', hBA, map_one])
  let y : G.Cˣ := ⟨x, x', hxx', hx'x⟩
  have hform : ∀ v v', s₀ * D.EF.baseChange ℚ (L.rep ((β⁻¹ : G.Cˣ) : G.C) (A v)) (A v') =
      (m : ℚ) * s₂ * D.EF.baseChange ℚ (L.rep ((β'⁻¹ : G.Cˣ) : G.C) v) v' := by
    intro v v'
    obtain ⟨a, u, ha, hu⟩ := hjs2 v
    obtain ⟨b, u', hb, hu'⟩ := hjs2 v'
    have e1 := hjF (w u) (w u')
    have e2 := hjF2 u u'
    have e3 : ((D'.EF (w u) (w u') : ℤ) : ℚ) = (m : ℚ) * (D''.EF u u' : ℤ) := by
      rw [hw u u']; push_cast; ring
    unfold formB at e1 e2
    rw [← hA, ← hA, ← hu, ← hu', map_nsmul, map_nsmul, map_nsmul] at e1
    rw [← hu, ← hu', map_nsmul] at e2
    simp only [map_nsmul, LinearMap.smul_apply, nsmul_eq_mul] at e1 e2
    have hab : (a : ℚ) * b ≠ 0 := mul_ne_zero (by exact_mod_cast ha) (by exact_mod_cast hb)
    apply mul_left_cancel₀ hab
    linear_combination -e1 + e3 + (m : ℚ) * e2
  have hnd : ∀ a : VQ D, (∀ v, D.EF.baseChange ℚ a v = 0) → a = 0 := by
    intro a ha
    obtain ⟨c, u, hc, hu⟩ := hjs (L.rep (β : G.C) a)
    have hinv : ∀ z : VQ D, L.rep ((β⁻¹ : G.Cˣ) : G.C) (L.rep (β : G.C) z) = z := by
      intro z
      rw [← Module.End.mul_apply, ← map_mul, Units.inv_mul, map_one, Module.End.one_apply]
    have hu0 : u = 0 := by
      refine D'.nondeg u fun u' => ?_
      have e := hjF u u'
      unfold formB at e
      rw [← hu, map_nsmul, hinv] at e
      simp only [map_nsmul, LinearMap.smul_apply, ha, smul_zero, mul_zero] at e
      exact_mod_cast e
    have h0 : c • L.rep (β : G.C) a = c • (0 : VQ D) := by rw [hu, hu0, map_zero, smul_zero]
    have := nsmul_canc hc h0
    rw [← hinv a, this, map_zero]
  set r : ℚ := (m : ℚ) * s₂ / s₀ with hr
  have hr0 : 0 < r := by
    have : (0 : ℚ) < m := by exact_mod_cast hm
    positivity
  have hs₀' : s₀ ≠ 0 := hs₀.ne'
  have hshsh : sh G (sh G x) = x := G.star_star x
  have hkey : sh G x * ((β⁻¹ : G.Cˣ) : G.C) * x = algebraMap ℚ G.C r * ((β'⁻¹ : G.Cˣ) : G.C) := by
    apply L.rep_inj
    refine LinearMap.ext fun v => ?_
    rw [← sub_eq_zero]
    refine hnd _ fun v' => ?_
    have e := hform v v'
    have e2 := L.adj (sh G x) (L.rep ((β⁻¹ : G.Cˣ) : G.C) (A v)) v'
    rw [hshsh, hx] at e2
    simp only [map_mul, Module.End.mul_apply, hx, AlgHom.commutes, Module.algebraMap_end_apply,
      map_sub, LinearMap.sub_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]
    rw [e2, hr]
    field_simp
    linear_combination e
  refine ⟨y, Units.mk0 r hr0.ne', hr0, ?_, fun u => ?_⟩
  · show x * (β' : G.C) * sh G x = algebraMap ℚ G.C r * (β : G.C)
    have h1 : x * (β' : G.C) * sh G x * (((β⁻¹ : G.Cˣ) : G.C) * x) = r • x := by
      calc x * (β' : G.C) * sh G x * (((β⁻¹ : G.Cˣ) : G.C) * x)
          = x * (β' : G.C) * (sh G x * ((β⁻¹ : G.Cˣ) : G.C) * x) := by simp only [_root_.mul_assoc]
        _ = r • (x * ((β' : G.C) * ((β'⁻¹ : G.Cˣ) : G.C))) := by
            rw [hkey, ← Algebra.smul_def, mul_smul_comm, _root_.mul_assoc]
        _ = r • x := by rw [Units.mul_inv, _root_.mul_one]
    calc x * (β' : G.C) * sh G x
        = x * (β' : G.C) * sh G x * (((β⁻¹ : G.Cˣ) : G.C) * (x * x') * (β : G.C)) := by
          rw [hxx', _root_.mul_one, Units.inv_mul, _root_.mul_one]
      _ = x * (β' : G.C) * sh G x * (((β⁻¹ : G.Cˣ) : G.C) * x) * (x' * (β : G.C)) := by
          simp only [_root_.mul_assoc]
      _ = r • (x * x' * (β : G.C)) := by rw [h1, smul_mul_assoc, _root_.mul_assoc]
      _ = algebraMap ℚ G.C r * (β : G.C) := by rw [hxx', _root_.one_mul, Algebra.smul_def]
  · show j (w u) = L.rep x (j'' u)
    rw [hx, hA]
end

