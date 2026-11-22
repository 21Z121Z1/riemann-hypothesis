import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.LevelChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1201
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelEqKN
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0992
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1159

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PCoordIso
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

namespace UpperTheory.Gal.W2

private theorem actY_inv_left {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} (L : Link D G) {β : G.Cˣ}
    (y : GlobalTheory.LKCx.grp G β) (w : VQ D) : actY L y⁻¹ (actY L y w) = w := by
  show L.rep ((y⁻¹ : GlobalTheory.LKCx.grp G β) : G.Cˣ × ℚˣ).1 (L.rep ((y : G.Cˣ × ℚˣ).1 : G.C) w) = w
  rw [← Module.End.mul_apply, ← map_mul]
  simp

private theorem perMove (hA : ActY) {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} (L : Link D G)
    {v : InfinitePlace G.F} {t₀ : D.F →+* ℂ} {ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ} {β : G.Cˣ}
    (RD : RDic L v β ρ t₀) (hs : sh G β = β) (y : GlobalTheory.LKCx.grp G β) {Q'' : VQ D →+ (Fin D.g → ℂ)}
    (hQ : IsPerQ L β ρ Q'') (z : GlobalTheory.LKCx.PosV G v β) (hr : RD.rel Q'' z.1) :
    ∃ (Q₁ : VQ D →+ (Fin D.g → ℂ)) (z₁ : GlobalTheory.LKCx.PosV G v β), IsPerQ L β ρ Q₁ ∧
      (∀ w, Q₁ (actY L y w) = Q'' w) ∧ RD.rel Q₁ z₁.1 ∧
      z₁.1 = (GlobalTheory.LKCx.toV G v β y : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ z.1 := by
  obtain ⟨-, -, h3, h4⟩ := hA p D G L β y
  let Q₁ : VQ D →+ (Fin D.g → ℂ) := Q''.comp (actY L y⁻¹).toAddMonoidHom
  have e : ∀ w, Q₁ (actY L y w) = Q'' w := fun w => by
    show Q'' (actY L y⁻¹ (actY L y w)) = _
    rw [actY_inv_left]
  obtain ⟨z₁, hz₁⟩ := h4 v z hs
  refine ⟨Q₁, z₁, h3 ρ Q'' Q₁ hQ e, e, ?_, hz₁⟩
  rw [hz₁]
  exact RD.equiv y Q'' Q₁ z.1 e hr

private theorem same_mk {p : ℕ} [Fact p.Prime] {G : HTGroup p} {v : InfinitePlace G.F} (B : GlobalTheory.LKCx.Form G)
    (K : Subgroup G.GAf) (K' : Subgroup (Gr G 1)) (a b : GlobalTheory.LKCx.Dat G v B.β) (y : GlobalTheory.LKCx.grp G B.β) (c : ℂ)
    (hc : c ≠ 0) (h1 : b.1.1⁻¹ * B.toAf y * a.1.1 ∈ K) (h2 : b.1.2⁻¹ * GlobalTheory.LKCx.toP1 G B.β y * a.1.2 ∈ K')
    (hz : b.2.1 = c • ((GlobalTheory.LKCx.toV G v B.β y : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ a.2.1)) :
    GlobalTheory.LKCx.Same G v B.β B.trivAf.choose B.trivAf.choose_spec.choose B.trivAf.choose_spec.choose_spec K K' a b := by
  refine ⟨y, ((b.1.1⁻¹ * B.toAf y * a.1.1)⁻¹, (b.1.2⁻¹ * GlobalTheory.LKCx.toP1 G B.β y * a.1.2)⁻¹), c,
    inv_mem h1, inv_mem h2, hc, ?_, hz⟩
  change b.1 = (B.toAf y, GlobalTheory.LKCx.toP1 G B.β y) * a.1 * _
  refine Prod.ext ?_ ?_
  · simp only [Prod.fst_mul]
    group
  · simp only [Prod.snd_mul]
    group

private theorem same_of_eq {p : ℕ} [Fact p.Prime] {G : HTGroup p} {v : InfinitePlace G.F} (B : GlobalTheory.LKCx.Form G)
    (K : Subgroup G.GAf) (K' : Subgroup (Gr G 1)) (a b : GlobalTheory.LKCx.Dat G v B.β)
    (h : (Quot.mk _ a : GlobalTheory.LKCx.Form.Pts v B K K') = Quot.mk _ b) :
    GlobalTheory.LKCx.Same G v B.β B.trivAf.choose B.trivAf.choose_spec.choose B.trivAf.choose_spec.choose_spec K K' b a := by
  have key : ∀ a b : GlobalTheory.LKCx.Dat G v B.β,
      Relation.EqvGen (GlobalTheory.LKCx.Same G v B.β B.trivAf.choose B.trivAf.choose_spec.choose
        B.trivAf.choose_spec.choose_spec K K') a b →
      (∃ y : GlobalTheory.LKCx.grp G B.β, y • GlobalTheory.CxUnfold.OrbitSumGen.pairOfDat G v B.β B.trivAf.choose
          B.trivAf.choose_spec.choose B.trivAf.choose_spec.choose_spec K K' a =
        GlobalTheory.CxUnfold.OrbitSumGen.pairOfDat G v B.β B.trivAf.choose
          B.trivAf.choose_spec.choose B.trivAf.choose_spec.choose_spec K K' b) ∧
      (∃ y : GlobalTheory.LKCx.grp G B.β, y • GlobalTheory.CxUnfold.OrbitSumGen.pairOfDat G v B.β B.trivAf.choose
          B.trivAf.choose_spec.choose B.trivAf.choose_spec.choose_spec K K' b =
        GlobalTheory.CxUnfold.OrbitSumGen.pairOfDat G v B.β B.trivAf.choose
          B.trivAf.choose_spec.choose B.trivAf.choose_spec.choose_spec K K' a) := by
    intro a b hab
    induction hab with
    | rel x y hxy =>
      obtain ⟨g, hg⟩ := (GlobalTheory.CxUnfold.OrbitSumGen.same_iff_smul _ _ _ _ _ _ _ _ x y).1 hxy
      exact ⟨⟨g, hg⟩, ⟨g⁻¹, by rw [← hg, inv_smul_smul]⟩⟩
    | refl x => exact ⟨⟨1, one_smul _ _⟩, ⟨1, one_smul _ _⟩⟩
    | symm x y _ ih => exact ⟨ih.2, ih.1⟩
    | trans x y z _ _ ih1 ih2 =>
      obtain ⟨⟨g1, hg1⟩, ⟨h1, hh1⟩⟩ := ih1
      obtain ⟨⟨g2, hg2⟩, ⟨h2, hh2⟩⟩ := ih2
      exact ⟨⟨g2 * g1, by rw [mul_smul, hg1, hg2]⟩, ⟨h1 * h2, by rw [mul_smul, hh2, hh1]⟩⟩
  exact (GlobalTheory.CxUnfold.OrbitSumGen.same_iff_smul _ _ _ _ _ _ _ _ b a).2 (key a b (Quot.eqvGen_exact h)).2

end UpperTheory.Gal.W2

private theorem ext_lemma {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} {L : Link D G} {β : G.Cˣ}
    {D' : PLat D.O D.inv} {j : D'.La →+ VQ D} (hj : IsPlace L β D' j) (Q Q₁ : VQ D →+ (Fin D.g → ℂ))
    (h : (Fin D.g → ℂ) ≃ₗ[ℂ] (Fin D.g → ℂ)) (hQ : ∀ u, Q (j u) = h (Q₁ (j u))) :
    ∀ w, Q w = h (Q₁ w) := by
  intro w
  obtain ⟨m, u, hm, hmu⟩ := hj.2.2.1 w
  have key : m • Q w = m • h (Q₁ w) := by
    rw [← map_nsmul Q, hmu, hQ, ← hmu, map_nsmul Q₁, map_nsmul h]
  exact smul_right_injective _ hm key

theorem UpperTheory.Gal.W2.coordIso_of :
    UpperTheory.Gal.W2.LatForm → UpperTheory.Gal.W2.LatIso → UpperTheory.Gal.W2.ActY → UpperTheory.Gal.W2.CoordIso := by
  intro hF hI hA p _ D G L v t₀ ρ PD RD N hN hNp D' t P D'' t'' P'' hc hc'' q q'' a a'' j j'' ha ha''
  obtain ⟨hpl, hca, hlp, Q, hQ, hQj, hr⟩ := ha
  obtain ⟨hpl'', hca'', hlp'', Q'', hQ'', hQj'', hr''⟩ := ha''
  constructor
  · rintro ⟨w, h, hw, hPh⟩
    obtain ⟨y, s, hs, hy, hjw⟩ := hF p D G L _ _ D' D'' j j'' hpl hpl'' w.toLinearMap 1 one_pos
      (by intro u u'; rw [_root_.one_mul]; exact hw.1 u u')
    have hjw' : ∀ u, j (w u) = L.rep (y : G.C) (j'' u) := hjw
    have hrel : GlobalTheory.LKCx.Form.Rel (Quot.out q'') (Quot.out q) := by
      refine ⟨y, (s : ℚ)⁻¹, inv_pos.mpr hs, ?_⟩
      rw [hy, ← _root_.mul_assoc, ← map_mul, inv_mul_cancel₀ (ne_of_gt hs), map_one, _root_.one_mul]
    have hq : q'' = q :=
      (Quot.out_eq (q'' : Quot GlobalTheory.LKCx.Form.Rel)).symm.trans
        ((Quot.sound hrel).trans (Quot.out_eq (q : Quot GlobalTheory.LKCx.Form.Rel)))
    subst hq
    let yy : GlobalTheory.LKCx.grp G (Quot.out q'').β := ⟨(y, s), hy, hs⟩
    obtain ⟨Q₁, z₁, hQ₁, hQ₁y, hr₁, hz₁⟩ := perMove hA L (RD _) (Quot.out q'').sym yy hQ'' a''.2 hr''
    have hext : ∃ h' : (Fin D.g → ℂ) ≃ₗ[ℂ] (Fin D.g → ℂ), ∀ w0, Q w0 = h' (Q₁ w0) := by
      refine ⟨h, ext_lemma hpl Q Q₁ h ?_⟩
      intro u
      obtain ⟨u'', rfl⟩ := w.surjective u
      rw [hQj, hPh, ← hQj'', ← hQ₁y, hjw']
      rfl
    obtain ⟨c, hc0, hac⟩ := ((RD _).uniq Q₁ Q z₁ a.2 hQ₁ hQ hr₁ hr).1 hext
    have hmem := (hI p D G L (Quot.out q'') (PD _) N hN hNp D' t D'' t'' j j'' a.1 a''.1 N N t t''
      hc hc'' hpl hpl'' hca hca'' hlp hlp'' yy).2 ⟨w, hw, hjw'⟩
    exact congrArg (Sigma.mk _)
      (Quot.sound (same_mk _ _ _ a'' a yy c hc0 hmem.1 hmem.2 (by rw [hac, hz₁]))).symm
  · intro heq
    obtain ⟨hq, hh⟩ := Sigma.mk.inj heq
    subst hq
    obtain ⟨y, k, c, hk1, hk2, hc0, hk, hz⟩ := same_of_eq _ _ _ a a'' (eq_of_heq hh)
    have hmem1 : a.1.1⁻¹ * (Quot.out q).toAf y * a''.1.1 ∈ L.KN N := by
      have e : a.1.1 = (Quot.out q).toAf y * a''.1.1 * k.1 := congrArg Prod.fst hk
      have e2 : ((Quot.out q).toAf y * a''.1.1 * k.1)⁻¹ * (Quot.out q).toAf y * a''.1.1 = k.1⁻¹ := by
        group
      rw [e, e2]
      exact inv_mem hk1
    have hmem2 : a.1.2⁻¹ * GlobalTheory.LKCx.toP1 G (Quot.out q).β y * a''.1.2 ∈ KHT p G.m G.n 1 G.Fw := by
      have e : a.1.2 = GlobalTheory.LKCx.toP1 G (Quot.out q).β y * a''.1.2 * k.2 := congrArg Prod.snd hk
      have e2 : (GlobalTheory.LKCx.toP1 G (Quot.out q).β y * a''.1.2 * k.2)⁻¹ * GlobalTheory.LKCx.toP1 G (Quot.out q).β y *
          a''.1.2 = k.2⁻¹ := by
        group
      rw [e, e2]
      exact inv_mem hk2
    obtain ⟨w, hw, hjw⟩ := (hI p D G L (Quot.out q) (PD _) N hN hNp D' t D'' t'' j j'' a.1 a''.1 N N t t''
      hc hc'' hpl hpl'' hca hca'' hlp hlp'' y).1 ⟨hmem1, hmem2⟩
    obtain ⟨Q₁, z₁, hQ₁, hQ₁y, hr₁, hz₁⟩ := perMove hA L (RD _) (Quot.out q).sym y hQ'' a''.2 hr''
    obtain ⟨h, hh'⟩ := ((RD _).uniq Q₁ Q z₁ a.2 hQ₁ hQ hr₁ hr).2 ⟨c, hc0, by rw [hz, hz₁]⟩
    refine ⟨w, h, hw, fun u => ?_⟩
    rw [← hQj, hjw, hh', hQ₁y, hQj'']
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PCoordKN
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

namespace UpperTheory.Gal.W2

section SlopeTestRemainingChoices

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} (L : Link D G)

private theorem smul_mem_laHat {c : AfP p} (hc : IsIntAf c) {v : AfP p ⊗[ℚ] VQ D} (hv : v ∈ LaHat D) :
    c • v ∈ LaHat D := by
  classical
  haveI := D.freeLa
  haveI := D.finLa
  let b := Module.Free.chooseBasis ℤ D.La
  apply KNLevel.mem_laHat_of_repr b
  intro i
  rw [map_smul, Finsupp.smul_apply, smul_eq_mul, KNLevel.isIntAf_iff]
  exact mul_mem ((KNLevel.isIntAf_iff _).mp hc)
    ((KNLevel.isIntAf_iff _).mp (KNLevel.repr_isIntAf b v hv i))

private theorem inAf_mem_laHat (a : D.La) : inAf D a ∈ LaHat D := by
  unfold inAf LaHat
  exact AddSubgroup.subset_closure ⟨1, a, (KNLevel.isIntAf_iff 1).mpr (one_mem _), rfl⟩

private theorem exists_den_act (g : G.GAf) :
    ∃ m : ℕ, 0 < m ∧ ∀ z ∈ LaHat D, m • L.actG g z ∈ LaHat D := by
  classical
  haveI := D.freeLa
  haveI := D.finLa
  let b := Module.Free.chooseBasis ℤ D.La
  let B := KNLevel.bA b
  obtain ⟨m, hm, hden⟩ := AfPCpctDen.exists_den p
    (Set.range fun ki : Module.Free.ChooseBasisIndex ℤ D.La × Module.Free.ChooseBasisIndex ℤ D.La =>
      B.repr (L.actG g (B ki.1)) ki.2) (Set.finite_range _).isCompact
  refine ⟨m, hm, fun z hz => ?_⟩
  have hy : ∀ k, m • L.actG g (B k) ∈ LaHat D := by
    intro k
    apply KNLevel.mem_laHat_of_repr b
    intro i
    rw [map_nsmul, Finsupp.smul_apply, nsmul_eq_mul, KNLevel.isIntAf_iff]
    exact hden _ ⟨(k, i), rfl⟩
  rw [← B.sum_repr z, map_sum, Finset.smul_sum]
  refine sum_mem fun k _ => ?_
  rw [LinearMap.map_smul, smul_comm m]
  exact smul_mem_laHat (KNLevel.repr_isIntAf b z hz k) (hy k)

private theorem rd_move (x : (AfP p ⊗[ℚ] G.C)ˣ) (h₁ h₂ : G.GAf) (w : VQ D) :
    rd L x h₂ w = L.actG (h₂⁻¹ * h₁) (rd L x h₁ w) := by
  simp only [rd]
  rw [← Module.End.mul_apply (L.actG (h₂⁻¹ * h₁)), ← map_mul, mul_inv_cancel_right]

private theorem stable (hd : RdDense) (x : (AfP p ⊗[ℚ] G.C)ˣ) (h₁ h₂ : G.GAf) (P : VQ D → Prop)
    (A₁ : ∀ w, P w ↔ rd L x h₁ w ∈ LaHat D) (A₂ : ∀ w, P w ↔ rd L x h₂ w ∈ LaHat D)
    (z : AfP p ⊗[ℚ] VQ D) (hz : z ∈ LaHat D) : L.actG (h₂⁻¹ * h₁) z ∈ LaHat D := by
  obtain ⟨m, hm, hden⟩ := exists_den_act L (h₂⁻¹ * h₁)
  obtain ⟨w, e, he, rfl⟩ := hd p D G L x h₁ m hm z
  have h1 : rd L x h₁ w ∈ LaHat D := by
    have := sub_mem hz (nsmul_mem he m)
    rwa [add_sub_cancel_right] at this
  have h2 : rd L x h₂ w ∈ LaHat D := (A₂ w).mp ((A₁ w).mpr h1)
  rw [map_add, map_nsmul, ← rd_move L x h₁ h₂ w]
  exact add_mem h2 (hden e he)

private theorem congOne_of_gen {N : ℕ} {g : G.GAf}
    (gen : ∀ a : D.La, ∃ u ∈ LaHat D, L.actG g (inAf D a) = inAf D a + N • u) : L.CongOne N g := by
  unfold Link.CongOne
  intro v hv
  unfold LaHat at hv
  induction hv using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨c, y, hc, rfl⟩ := hz
    obtain ⟨u, hu, hgu⟩ := gen y
    have hcy : c ⊗ₜ[ℚ] ((1 : ℚ) ⊗ₜ[ℤ] y) = c • inAf D y := by
      rw [inAf, TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
    refine ⟨c • u, smul_mem_laHat hc hu, ?_⟩
    rw [hcy, LinearMap.map_smul, hgu, smul_add, smul_comm c N u]
  | zero => exact ⟨0, zero_mem _, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨w₁, hw₁, e₁⟩ := hy
    obtain ⟨w₂, hw₂, e₂⟩ := hz
    exact ⟨w₁ + w₂, add_mem hw₁ hw₂, by rw [map_add, e₁, e₂, smul_add]; abel⟩
  | neg y _ hy =>
    obtain ⟨w, hw, e⟩ := hy
    exact ⟨-w, neg_mem hw, by rw [map_neg, e, neg_add, smul_neg]⟩

end SlopeTestRemainingChoices

theorem coordKN_of : RdDense → CoordKN := by
  intro hd p _ D G L x N hN hcop D' t j h₁ h₂ hc1
  have memOf : ∀ {g : G.GAf}, L.CongOne N g → ∀ v ∈ LaHat D, L.actG g v ∈ LaHat D := by
    intro g hC v hv
    obtain ⟨w, hw, e⟩ := hC v hv
    rw [e]
    exact add_mem hv (nsmul_mem hw N)
  have cong : ∀ k₁ k₂ : G.GAf, IsCoordA L x N D' t j k₁ → IsCoordA L x N D' t j k₂ →
      L.CongOne N (k₂⁻¹ * k₁) := by
    intro k₁ k₂ hk₁ hk₂
    have hst : ∀ z ∈ LaHat D, L.actG (k₂⁻¹ * k₁) z ∈ LaHat D :=
      stable L hd x k₁ k₂ (fun w => ∃ r u, p ^ r • w = j u) hk₁.1 hk₂.1
    apply congOne_of_gen L
    intro a
    obtain ⟨w₁, hw₁, e₁⟩ := hk₁.2 a
    obtain ⟨w₂, hw₂, e₂⟩ := hk₂.2 a
    refine ⟨w₂ - L.actG (k₂⁻¹ * k₁) w₁, sub_mem hw₂ (hst w₁ hw₁), ?_⟩
    have e₃ := rd_move L x k₁ k₂ (j (t a))
    rw [e₂, e₁, map_add, map_nsmul] at e₃
    rw [smul_sub, ← add_sub_assoc, e₃]
    abel
  constructor
  · intro hc2
    exact ⟨cong h₁ h₂ hc1 hc2, by rw [mul_inv_rev, inv_inv]; exact cong h₂ h₁ hc2 hc1⟩
  · intro hg
    obtain ⟨hC, hCi⟩ := hg
    have hinv : (h₂⁻¹ * h₁)⁻¹ = h₁⁻¹ * h₂ := by rw [mul_inv_rev, inv_inv]
    refine ⟨fun w => ?_, fun a => ?_⟩
    · rw [hc1.1 w]
      constructor
      · intro hw
        rw [rd_move L x h₁ h₂ w]
        exact memOf hC _ hw
      · intro hw
        rw [rd_move L x h₂ h₁ w, ← hinv]
        exact memOf hCi _ hw
    · obtain ⟨w₁, hw₁, e₁⟩ := hc1.2 a
      obtain ⟨w₃, hw₃, e₃⟩ := hC _ (inAf_mem_laHat a)
      refine ⟨w₃ + L.actG (h₂⁻¹ * h₁) w₁, add_mem hw₃ (memOf hC _ hw₁), ?_⟩
      rw [rd_move L x h₁ h₂, e₁, map_add, map_nsmul, e₃, smul_add, add_assoc]

end UpperTheory.Gal.W2
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PCoordMove
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

private theorem rd_add' {p : ℕ} [Fact (Nat.Prime p)] {D : UPel.HT.Datum p} {G : HTGroup p}
    (L : Link D G) (x : (AfP p ⊗[ℚ] G.C)ˣ) (h : G.GAf) (a b : VQ D) :
    rd L x h (a + b) = rd L x h a + rd L x h b := by
  simp only [rd, TensorProduct.tmul_add, map_add]

private theorem rd_nsmul' {p : ℕ} [Fact (Nat.Prime p)] {D : UPel.HT.Datum p} {G : HTGroup p}
    (L : Link D G) (x : (AfP p ⊗[ℚ] G.C)ˣ) (h : G.GAf) (N : ℕ) (a : VQ D) :
    rd L x h (N • a) = N • rd L x h a := by
  induction N with
  | zero => simp only [zero_smul, rd, TensorProduct.tmul_zero, map_zero]
  | succ n ih => rw [succ_nsmul, rd_add', ih, succ_nsmul]

theorem UpperTheory.Gal.W2.coordMove_of :
    UpperTheory.Gal.W2.CoordMove := by
  intro p _ D G L v t₀ ρ B PD RD N D' t P D'' t'' P'' w hw hP j j'' hj a ha
  obtain ⟨hiso, hmark⟩ := hw
  obtain ⟨⟨hinj, hact, hsurj, s, hs, hform⟩, ⟨hA1, hA2⟩, hloc, Q, hQ, hQj, hrel⟩ := ha
  have key : ∀ w0 : VQ D, (∃ u : D'.La, w0 = j u) ↔ ∃ u : D''.La, w0 = j'' u := by
    intro w0
    constructor
    · rintro ⟨u, rfl⟩
      exact ⟨w.symm u, by rw [hj, LinearEquiv.apply_symm_apply]⟩
    · rintro ⟨u, rfl⟩
      exact ⟨w u, hj u⟩
  refine ⟨⟨?_, ?_, ?_, s, hs, ?_⟩, ⟨?_, ?_⟩, ?_, Q, hQ, ?_, hrel⟩
  · intro u u' huu
    rw [hj, hj] at huu
    exact w.injective (hinj huu)
  · intro c u
    rw [hj, hj, map_smul, hact]
  · intro w0
    obtain ⟨m, u, hm, hmu⟩ := hsurj w0
    exact ⟨m, w.symm u, hm, by rw [hj, LinearEquiv.apply_symm_apply, hmu]⟩
  · intro u u'
    rw [hj, hj, ← hform, hiso]
  · intro w0
    rw [← hA1 w0]
    constructor
    · rintro ⟨r, u, hu⟩
      exact ⟨r, w u, by rw [hu, hj]⟩
    · rintro ⟨r, u, hu⟩
      exact ⟨r, w.symm u, by rw [hu, hj, LinearEquiv.apply_symm_apply]⟩
  · intro a0
    obtain ⟨e, he⟩ := hmark a0
    obtain ⟨w1, hw1, hw1e⟩ := hA2 a0
    have he' : rd L (trivX B) a.1.1 (j e) ∈ LaHat D := (hA1 (j e)).1 ⟨0, e, by simp⟩
    refine ⟨w1 + rd L (trivX B) a.1.1 (j e), add_mem hw1 he', ?_⟩
    rw [hj, he, map_add, map_nsmul, rd_add', rd_nsmul', hw1e, smul_add, add_assoc]
  · intro w0
    rw [← hloc w0]
    constructor
    · rintro ⟨m, u, hm, hu⟩
      exact ⟨m, w u, hm, by rw [hu, hj]⟩
    · rintro ⟨m, u, hm, hu⟩
      exact ⟨m, w.symm u, hm, by rw [hu, hj, LinearEquiv.apply_symm_apply]⟩
  · intro u
    rw [hj, hQj, hP]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PCoordOcc
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

theorem UpperTheory.Gal.W2.coordOcc_of :
    UpperTheory.Gal.W2.WitOfAd → UpperTheory.Gal.W2.PlacePer → UpperTheory.Gal.W2.CoordOcc := by
  intro hW hP p _ D G L _ _ v _ t₀ _ ρ _ PD RD N hN hNp B a
  obtain ⟨D', t, j, hcls, hpl, hco, hloc⟩ :=
    hW p D G L B N hN hNp a.1.1 ((PD B).lat a.1.2) ((PD B).isLat _) ((PD B).perf _)
  obtain ⟨Q, hQ, hrel⟩ := (RD B).per a.2
  have hev : Even (Module.finrank ℚ D.F) := by
    rw [← NumberField.InfinitePlace.card_add_two_mul_card_eq_rank]
    simp [NumberField.IsTotallyComplex.nrRealPlaces_eq_zero]
  have hg : 2 * D.g = Module.finrank ℤ D.La := by
    obtain ⟨k, hk⟩ := hev
    rw [D.rankLa, Datum.g, hk, ← two_mul, mul_left_comm, Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]
  exact ⟨D', t, Q.comp j, j, hcls, (hP p D G L B.β ρ D' j hpl).2 Q hQ hg, hpl, hco, hloc, Q, hQ,
    fun u => rfl, hrel⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PFixLine
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

private theorem herm_pos_toV_mulVec_of_pos {p : ℕ} [Fact p.Prime] (G : HTGroup p) (v : InfinitePlace G.F) (β : G.Cˣ)
    (y : LKCx.grp G β) (z : Fin G.n → ℂ) (hz : 0 < (star z ⬝ᵥ LKCx.herm G v β *ᵥ z).re) :
    0 < (star (↑(LKCx.toV G v β y) *ᵥ z) ⬝ᵥ LKCx.herm G v β *ᵥ (↑(LKCx.toV G v β y) *ᵥ z)).re := by
  have hM : (↑(LKCx.toV G v β y) : Matrix (Fin G.n) (Fin G.n) ℂ) = G.psi v ↑(↑y : G.Cˣ × ℚˣ).1 := rfl
  have hs := GlobalTheory.ArchBound.herm_sim G β y v
  have hpos : (0 : ℝ) < ((↑(↑y : G.Cˣ × ℚˣ).2 : ℚ) : ℝ) := by exact_mod_cast y.2.2
  rw [hM, Matrix.star_mulVec, Matrix.mulVec_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
    ← Matrix.mul_assoc, hs, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, Complex.re_ofReal_mul]
  exact mul_pos hpos hz

private theorem actY_actY_inv {p : ℕ} [Fact p.Prime] {D : UPel.HT.Datum p} {G : HTGroup p} (L : Link D G)
    {β : G.Cˣ} (a : LKCx.grp G β) (w : VQ D) : actY L a (actY L a⁻¹ w) = w := by
  show L.rep _ (L.rep _ w) = w
  rw [← Module.End.mul_apply, ← map_mul]
  have h1 : ((↑(↑a : G.Cˣ × ℚˣ).1 : G.C) * ↑(↑a⁻¹ : G.Cˣ × ℚˣ).1) = 1 := by
    rw [← Units.val_mul, ← Prod.fst_mul, ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one, Prod.fst_one,
      Units.val_one]
  rw [h1, map_one, Module.End.one_apply]

theorem UpperTheory.Gal.W2.fixLine_of :
    UpperTheory.Gal.W2.ActY → UpperTheory.Gal.W2.FixLine := by
  intro hA p _ D G L v t₀ ρ β RD Q z hQ hrel y
  have hz0 : z.1 ≠ 0 := by
    intro h0
    have h1 := z.2
    rw [h0] at h1
    simp at h1
  have hinvmul : ∀ (y' : LKCx.grp G β) (x : Fin G.n → ℂ),
      (LKCx.toV G v β y'⁻¹).val *ᵥ ((LKCx.toV G v β y').val *ᵥ x) = x := by
    intro y' x
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one,
      Matrix.one_mulVec]
  have hne : ∀ (y' : LKCx.grp G β) (c : ℂ), (LKCx.toV G v β y').val *ᵥ z.1 = c • z.1 → c ≠ 0 := by
    rintro y' c hc rfl
    rw [zero_smul] at hc
    apply hz0
    rw [← hinvmul y' z.1, hc, Matrix.mulVec_zero]
  have inv : ∀ y' : LKCx.grp G β, LKCx.FixL G v β y' z.1 → LKCx.FixL G v β y'⁻¹ z.1 := by
    rintro y' ⟨c, hc⟩
    have hc0 := hne y' c hc
    have h1 : z.1 = c • ((LKCx.toV G v β y'⁻¹).val *ᵥ z.1) := by
      rw [← Matrix.mulVec_smul, ← hc, hinvmul]
    refine ⟨c⁻¹, ?_⟩
    calc (LKCx.toV G v β y'⁻¹).val *ᵥ z.1
        = c⁻¹ • (c • ((LKCx.toV G v β y'⁻¹).val *ᵥ z.1)) := by rw [smul_smul, inv_mul_cancel₀ hc0, one_smul]
      _ = c⁻¹ • z.1 := by rw [← h1]
  let zi : LKCx.PosV G v β := ⟨(LKCx.toV G v β y⁻¹).val *ᵥ z.1, herm_pos_toV_mulVec_of_pos G v β y⁻¹ z.1 z.2⟩
  let Q₂ : VQ D →+ Fin D.g → ℂ := Q.comp (actY L y).toAddMonoidHom
  have hQ₂ : ∀ w, Q₂ w = Q (actY L y w) := fun w => rfl
  have hback : ∀ w, Q₂ (actY L y⁻¹ w) = Q w := by
    intro w
    rw [hQ₂, actY_actY_inv]
  have hper : IsPerQ L β ρ Q₂ := (hA p D G L β y⁻¹).2.2.1 ρ Q Q₂ hQ hback
  have hrel₂ : RD.rel Q₂ zi.1 := RD.equiv y⁻¹ Q Q₂ z.1 hback hrel
  have key := RD.uniq Q Q₂ z zi hQ hper hrel hrel₂
  refine ⟨⟨fun hF => ?_, fun ⟨H, hH⟩ => ?_⟩, inv y⟩
  · obtain ⟨c, hc⟩ := inv y hF
    obtain ⟨h, hh⟩ := key.mpr ⟨c, hne _ c hc, hc⟩
    refine ⟨LinearMap.toMatrix' (h : (Fin D.g → ℂ) →ₗ[ℂ] Fin D.g → ℂ), fun w => ?_⟩
    rw [LinearMap.toMatrix'_mulVec, ← hQ₂, hh w]
    rfl
  · have hsurj : Function.Surjective (Matrix.toLin' H) := by
      rw [← LinearMap.range_eq_top]
      have hle : Submodule.span ℝ (Set.range ⇑Q) ≤ (LinearMap.range (Matrix.toLin' H)).restrictScalars ℝ := by
        rw [Submodule.span_le]
        rintro _ ⟨w, rfl⟩
        refine ⟨Q (actY L y⁻¹ w), ?_⟩
        rw [Matrix.toLin'_apply, ← hH, actY_actY_inv]
      rw [hQ.2.1] at hle
      exact eq_top_iff.mpr (fun x _ => hle (Submodule.mem_top : x ∈ (⊤ : Submodule ℝ (Fin D.g → ℂ))))
    have hinj := LinearMap.injective_iff_surjective.mpr hsurj
    obtain ⟨c, hc0, hc⟩ := key.mp ⟨LinearEquiv.ofBijective (Matrix.toLin' H) ⟨hinj, hsurj⟩, fun w => by
      show Q₂ w = Matrix.toLin' H (Q w)
      rw [Matrix.toLin'_apply, hQ₂, hH]⟩
    have h2 := inv y⁻¹ ⟨c, hc⟩
    rwa [inv_inv] at h2
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PRdAct
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical

namespace UpperTheory.Gal.W2

private theorem actOn_inC {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} (L : Link D G) (c : G.C) (w : VQ D) :
    actOn L.rep (AfP p) (inC G (AfP p) c) ((1 : AfP p) ⊗ₜ w) = (1 : AfP p) ⊗ₜ (L.rep c w) := by
  simp only [actOn, inC, RingHom.coe_coe, Algebra.TensorProduct.includeRight_apply]
  erw [Algebra.TensorProduct.lift_tmul]
  simp only [map_one, one_mul, Module.End.baseChangeHom, AlgHom.comp_apply]
  exact LinearMap.baseChange_tmul _ _ _

private theorem actG_toAf {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} (L : Link D G) (B : GlobalTheory.LKCx.Form G)
    (y : GlobalTheory.LKCx.grp G B.β) (w : VQ D) :
    L.actG (B.toAf y) (actOn L.rep (AfP p) (trivX B : AfP p ⊗[ℚ] G.C) ((1 : AfP p) ⊗ₜ w)) =
      actOn L.rep (AfP p) (trivX B : AfP p ⊗[ℚ] G.C) ((1 : AfP p) ⊗ₜ (L.rep (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) w)) := by
  have hval : (L.actG (B.toAf y) : Module.End (AfP p) (AfP p ⊗[ℚ] VQ D))
      = actOn L.rep (AfP p) ((trivX B : AfP p ⊗[ℚ] G.C) * inC G (AfP p) (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)
          * (((trivX B)⁻¹ : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C)) := rfl
  rw [hval, ← Module.End.mul_apply, ← map_mul,
    show (trivX B : AfP p ⊗[ℚ] G.C) * inC G (AfP p) (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)
          * (((trivX B)⁻¹ : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C) * (trivX B : AfP p ⊗[ℚ] G.C)
        = (trivX B : AfP p ⊗[ℚ] G.C) * inC G (AfP p) (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) by
      simp [mul_assoc],
    map_mul, Module.End.mul_apply, actOn_inC]

theorem rdAct_of : RdAct := by
  intro p _ D G L B y h₁ h₂ w
  simp only [rd, actY]
  conv_rhs =>
    rw [← Module.End.mul_apply, ← map_mul, _root_.mul_assoc, _root_.mul_assoc, _root_.mul_inv_cancel, _root_.mul_one, map_mul,
      Module.End.mul_apply, actG_toAf]

end UpperTheory.Gal.W2
end
end

