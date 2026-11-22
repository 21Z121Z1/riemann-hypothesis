import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartFH
import ReciprocityTheory.DualLattices.Bundle0026
import ReciprocityTheory.DualLattices.Bundle0015
import ReciprocityTheory.DualLattices.Bundle0033
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.LePreimageOfNil
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.IsEigBasisIff
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0034
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0036
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0022
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0020
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0013
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0037
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ToricPointExtensionTangentSeqSplitExact

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsFormalGroupSeriesToricPointExtension
section
set_option autoImplicit false
noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChF

private theorem chi_ext {X S : Type} [AddCommGroup X] [CommRing S] {r : ℕ} (β : Module.Basis (Fin r) ℤ X)
    (χ χ' : Multiplicative X →* Sˣ)
    (h : ∀ j, (χ (Multiplicative.ofAdd (β j)) : S) = χ' (Multiplicative.ofAdd (β j))) : χ = χ' := by
  have : (MonoidHom.toAdditiveRight χ).toIntLinearMap = (MonoidHom.toAdditiveRight χ').toIntLinearMap :=
    β.ext fun j => congrArg Additive.ofMul (Units.ext (h j))
  refine MonoidHom.ext fun y => ?_
  exact congrArg Additive.toMul (LinearMap.congr_fun this y.toAdd)

private theorem chi_ex {X S : Type} [AddCommGroup X] [CommRing S] {r : ℕ} (β : Module.Basis (Fin r) ℤ X)
    (t : Fin r → S) (ht : ∀ i, IsNilpotent (t i)) :
    ∃ χ : Multiplicative X →* Sˣ, ∀ j, (χ (Multiplicative.ofAdd (β j)) : S) = 1 + t j := by
  refine ⟨MonoidHom.toAdditiveRight.symm (β.constr ℤ
    (fun j => Additive.ofMul (ht j).isUnit_one_add.unit)).toAddMonoidHom, fun j => ?_⟩
  change ((Additive.toMul (β.constr ℤ (fun j => Additive.ofMul (ht j).isUnit_one_add.unit) (β j)) : Sˣ) : S) = _
  rw [Module.Basis.constr_basis]
  rfl

private def pairAlg (R : Type) {S : Type} [CommRing R] [CommRing S] [Algebra R S] (J : Ideal S) :
    Subalgebra R (S × S) where
  carrier := {p | p.2 - p.1 ∈ J}
  mul_mem' := fun {a b} ha hb => by
    have : (a * b).2 - (a * b).1 = a.2 * (b.2 - b.1) + (a.2 - a.1) * b.1 := by simp; ring
    change _ ∈ J
    rw [this]
    exact J.add_mem (J.mul_mem_left _ hb) (J.mul_mem_right _ ha)
  add_mem' := fun {a b} ha hb => by
    have : (a + b).2 - (a + b).1 = (a.2 - a.1) + (b.2 - b.1) := by simp; ring
    change _ ∈ J
    rw [this]
    exact J.add_mem ha hb
  algebraMap_mem' := fun c => by
    change _ ∈ J
    simp

private theorem coord_ex {R : Type} [CommRing R] {I : Ideal R} {G B : Over (Spec (CommRingCat.of R))} [GrpObj G]
    [GrpObj B] {X : Type} [AddCommGroup X] (E : PtExt I G B X) {d r : ℕ} {F : Fin d → PS R 2 d} {x : Fam G d}
    (hx : NilChart G F x) (β : Module.Basis (Fin r) ℤ X) (S : Type) [CommRing S] [Algebra R S]
    (h : ∃ k, Kills I k S) (t : Fin r → S) (ht : ∀ i, IsNilpotent (t i)) :
    ∃ b : Fin d → S, (∀ i, IsNilpotent (b i)) ∧ ∀ χ : Multiplicative X →* Sˣ,
      (∀ j, (χ (Multiplicative.ofAdd (β j)) : S) = 1 + t j) → E.i S h χ = x S b := by
  let J : Ideal S := Ideal.span (Set.range t)
  obtain ⟨N, hN⟩ : IsNilpotent J := by
    refine (Ideal.FG.isNilpotent_iff_le_nilradical ⟨(Set.finite_range t).toFinset, by simp [J]⟩).2 ?_
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact ht i
  let P : Type := pairAlg R J
  let ρ : P →ₐ[R] S := (AlgHom.fst R S S).comp (pairAlg R J).val
  let τ : P →ₐ[R] S := (AlgHom.snd R S S).comp (pairAlg R J).val
  let σ : S →ₐ[R] P := ((AlgHom.id R S).prod (AlgHom.id R S)).codRestrict _ (fun y => by
    change _ ∈ J
    simp)
  have hinj : ∀ p : P, ρ p = 0 → τ p = 0 → p = 0 := fun p h1 h2 => Subtype.ext (Prod.ext h1 h2)
  have hker : IsNilpotent (RingHom.ker ρ) := by
    refine ⟨N + 1, ?_⟩
    rw [Ideal.zero_eq_bot, eq_bot_iff]
    intro p hp
    have h1 : RingHom.ker ρ ≤ J.comap τ := fun q hq => by
      have h2 : τ q - ρ q ∈ J := q.2
      rw [RingHom.mem_ker] at hq
      rwa [hq, sub_zero] at h2
    have h2 := Ideal.pow_le_self (I := RingHom.ker ρ) (Nat.succ_ne_zero N) hp
    have h3 := Ideal.le_comap_pow τ (N + 1) (Ideal.pow_right_mono h1 (N + 1) hp)
    rw [pow_succ, hN, zero_mul, Ideal.mem_comap, Ideal.zero_eq_bot, Ideal.mem_bot] at h3
    exact hinj p h2 h3
  have hP : ∃ k, Kills I k P := by
    obtain ⟨k, hk⟩ := h
    exact ⟨k, fun c hc => hinj _ (by rw [AlgHom.commutes, hk c hc]) (by rw [AlgHom.commutes, hk c hc])⟩
  let u : Fin r → P := fun j => ⟨(0, t j), by
    change t j - 0 ∈ J
    rw [sub_zero]
    exact Ideal.subset_span ⟨j, rfl⟩⟩
  have hnil : ∀ p : P, ρ p = 0 → IsNilpotent p := fun p hp => by
    obtain ⟨n, hn⟩ := hker
    have := Ideal.pow_mem_pow (show p ∈ RingHom.ker ρ from hp) n
    rw [hn] at this
    exact ⟨n, this⟩
  obtain ⟨χ₁, hχ₁⟩ := chi_ex β u (fun j => hnil _ rfl)
  have h1 : (Units.map (ρ : P →* S)).comp χ₁ = 1 := chi_ext β _ _ fun j => by
    change ρ (χ₁ _ : P) = 1
    rw [hχ₁, map_add, map_one]
    exact add_zero _
  obtain ⟨a, ha, hz⟩ := hx.surj P S ρ σ (AlgHom.ext fun _ => rfl) hker (E.i P hP χ₁)
    (by rw [← E.i_nat P S ρ hP h, h1, map_one])
  refine ⟨fun i => τ (a i), fun i => (hnil _ (ha i)).map τ, fun χ hχ => ?_⟩
  rw [← hx.nat P S τ a (fun i => hnil _ (ha i)), ← hz, ← E.i_nat P S τ hP h]
  congr 1
  refine chi_ext β _ _ fun j => ?_
  change _ = τ (χ₁ _ : P)
  rw [hχ₁, map_add, map_one, hχ]
  rfl

theorem exists_series_torus : ∀ (R : Type) [CommRing R] (I : Ideal R) [IsAdicComplete I R] (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (B : Over (Spec (CommRingCat.of R))) [GrpObj B] [IsCommMonObj B] (X : Type) [AddCommGroup X] (E : PtExt I G B X) (d g : ℕ) (F : FGLaw R d) (FB : FGLaw R g) (x : Fam G d) (xB : Fam B g), NilChart G F.F x → NilChart B FB.F xB → ∀ (r : ℕ) (β : Module.Basis (Fin r) ℤ X), ∃ J : Fin d → PS R 1 r, IsHomF (gmF R r) F.F J ∧ (∀ (S : Type) [CommRing S] [Algebra R S] (h : ∃ k, Kills I k S) (χ : Multiplicative X →* Sˣ) (t : Fin r → S), (∀ i, IsNilpotent (t i)) → (∀ j, (χ (Multiplicative.ofAdd (β j)) : S) = 1 + t j) → E.i S h χ = x S (fun j => nv (algebraMap R S) (J j) ![t])) := by
  intro R _ I hI G _ _ B _ _ X _ E d g F FB x xB hx _ r β
  classical
  have hc : ∀ (S : Type) [CommRing S] [Algebra R S] (t : Fin r → S), ∃ b : Fin d → S,
      ∀ h : ∃ k, Kills I k S, (∀ i, IsNilpotent (t i)) → (∀ i, IsNilpotent (b i)) ∧ ∀ χ : Multiplicative X →* Sˣ,
      (∀ j, (χ (Multiplicative.ofAdd (β j)) : S) = 1 + t j) → E.i S h χ = x S b := by
    intro S _ _ t
    by_cases h : (∃ k, Kills I k S) ∧ ∀ i, IsNilpotent (t i)
    · obtain ⟨b, hb⟩ := coord_ex E hx β S h.1 t h.2
      exact ⟨b, fun _ _ => hb⟩
    · exact ⟨0, fun h1 h2 => absurd ⟨h1, h2⟩ h⟩
  choose c hc using hc
  have hJ : ∀ j : Fin d, ∃ f : PS R 1 r, ∀ (S : Type) [CommRing S] [Algebra R S] (a : Fin 1 → Fin r → S),
      True → (∃ k, Kills I k S) → (∀ i j, IsNilpotent (a i j)) → c S (a 0) j = nv (algebraMap R S) f a := by
    intro j
    refine exists_series_of_natural R I hI 1 r (fun _ _ _ => True) (fun _ _ => trivial) (fun S _ _ a => c S (a 0) j) ?_
    intro S _ _ S' _ _ φ a _ _ _ h ha
    have h' : ∃ k, Kills I k S' := by
      obtain ⟨k, hk⟩ := h
      exact ⟨k, fun c hc => by rw [← φ.commutes, hk c hc, map_zero]⟩
    obtain ⟨χ, hχ⟩ := chi_ex β (a 0) (ha 0)
    obtain ⟨h1, h2⟩ := hc S (a 0) h (ha 0)
    obtain ⟨h3, h4⟩ := hc S' (fun j => φ (a 0 j)) h' (fun i => (ha 0 i).map φ)
    have h5 := h4 ((Units.map (φ : S →* S')).comp χ) fun j => by
      change φ (χ _ : S) = _
      rw [hχ, map_add, map_one]
    rw [E.i_nat S S' φ h h', h2 χ hχ, hx.nat S S' φ _ h1] at h5
    exact congrFun (hx.inj S' _ _ (fun i => (h1 i).map φ) h3 h5) j
  choose J hJ using hJ
  have hJ' : ∀ (S : Type) [CommRing S] [Algebra R S] (t : Fin r → S), (∃ k, Kills I k S) →
      (∀ i, IsNilpotent (t i)) → (fun j => nv (algebraMap R S) (J j) ![t]) = c S t := by
    intro S _ _ t h ht
    funext j
    exact (hJ j S ![t] trivial h (fun i => by fin_cases i; exact ht)).symm
  have h0 : ∀ j, MvPowerSeries.constantCoeff (J j) = 0 := by
    intro j
    have : (MvPowerSeries.C (MvPowerSeries.constantCoeff (J j)) : PS R 1 r) = 0 := by
      refine eq_of_nv_eq R I inferInstance 1 r _ _ fun S _ _ k hk _ a ha => ?_
      obtain ⟨ψ, h1, h2, -⟩ := (nv_calculus R S (algebraMap R S) 1 r a ha).1
      rw [← h1, ← h1, h2, map_zero]
      have hz : ∀ i : Fin r, IsNilpotent ((0 : Fin r → S) i) := fun _ => IsNilpotent.zero
      obtain ⟨h3, h4⟩ := hc S 0 ⟨k, hk⟩ hz
      have h5 := h4 1 (fun j => by simp)
      rw [map_one, ← hx.zero S] at h5
      have h6 := congrFun ((hJ' S 0 ⟨k, hk⟩ hz).trans
        (hx.inj S _ _ (fun _ => IsNilpotent.zero) h3 h5).symm) j
      rw [(nv_calculus R S (algebraMap R S) 1 r ![0] (fun i => by fin_cases i; exact hz)).2.2.2.2.2
        (fun i _ i' _ => by fin_cases i; simp)] at h6
      simpa using h6
    simpa using congrArg MvPowerSeries.constantCoeff this
  refine ⟨J, ⟨h0, fun j => ?_⟩, fun S _ _ h χ t ht hχ => ?_⟩
  · refine eq_of_nv_eq R I inferInstance 2 r _ _ fun S _ _ k hk _ a ha => ?_
    have h : ∃ k, Kills I k S := ⟨k, hk⟩
    obtain ⟨⟨ψ, hψ, -, hX⟩, -, hs, -⟩ := nv_calculus R S (algebraMap R S) 2 r a ha
    have hev : ∀ (p : Fin r → PS R 2 r) (t : Fin r → S), (∀ i, MvPowerSeries.constantCoeff (p i) = 0) →
        (∀ i, ψ (p i) = t i) → (∀ i, IsNilpotent (t i)) →
        ∀ i, nv (algebraMap R S) (ev (n := 2) ![p] (J i)) a = c S t i := by
      intro p t hp hpt ht i
      rw [← hJ' S t h ht]
      refine (hs 1 r ![p] (J i) (fun i => by fin_cases i; exact hp)).trans ?_
      congr 1
      funext i j
      fin_cases i
      exact (hψ _).symm.trans (hpt j)
    have hcc : ∀ (l : Fin 2) (i : Fin d), MvPowerSeries.constantCoeff (ev (n := 2) ![pt R r l] (J i)) = 0 := by
      intro l i
      have hp : ∀ q : Fin 1 × Fin r, MvPowerSeries.constantCoeff ((![pt R r l] : Fin 1 → Pt R 2 r) q.1 q.2) = 0 := by
        rintro ⟨q, q'⟩
        fin_cases q
        simp [pt]
      exact MvPowerSeries.constantCoeff_subst_eq_zero (MvPowerSeries.hasSubst_of_constantCoeff_zero hp) hp (h0 i)
    have hn : ∀ i, IsNilpotent (a 0 i + a 1 i + a 0 i * a 1 i) := fun i =>
      (Commute.all _ _).isNilpotent_add ((Commute.all _ _).isNilpotent_add (ha 0 i) (ha 1 i))
        ((Commute.all _ _).isNilpotent_mul_left (ha 1 i))
    rw [hev (gmF R r) _ (fun i => by simp [gmF]) (fun i => by simp [gmF, hX]) hn,
      hs _ _ _ _ (fun l => by fin_cases l <;> exact hcc _)]
    obtain ⟨χ₀, hχ₀⟩ := chi_ex β (a 0) (ha 0)
    obtain ⟨χ₁, hχ₁⟩ := chi_ex β (a 1) (ha 1)
    obtain ⟨n0, e0⟩ := hc S (a 0) h (ha 0)
    obtain ⟨n1, e1⟩ := hc S (a 1) h (ha 1)
    obtain ⟨n2, e2⟩ := hc S _ h hn
    have e3 := e2 (χ₀ * χ₁) fun j => by
      rw [MonoidHom.mul_apply, Units.val_mul, hχ₀, hχ₁]
      ring
    rw [map_mul, e0 _ hχ₀, e1 _ hχ₁, hx.law S _ _ n0 n1] at e3
    have n3 : ∀ k, IsNilpotent (nv (algebraMap R S) (F.F k) ![c S (a 0), c S (a 1)]) := fun k =>
      ((nv_calculus R S (algebraMap R S) 2 d _ (fun l => by
        fin_cases l
        · exact n0
        · exact n1)).2.1 _ (F.const k)).1
    rw [← congrFun (hx.inj S _ _ n3 n2 e3) j]
    congr 1
    funext l i
    fin_cases l
    · exact (hev (pt R r 0) (a 0) (fun i => by simp [pt]) (fun i => hX (0, i)) (ha 0) i).symm
    · exact (hev (pt R r 1) (a 1) (fun i => by simp [pt]) (fun i => hX (1, i)) (ha 1) i).symm
  · rw [hJ' S t h ht]
    exact (hc S t h ht).2 χ hχ

end GlobalTheory.ChF
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsNilpotentGroupChartSmoothCommGroup
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChF

private lemma nv_eq_nEval {R S : Type} [CommRing R] [CommRing S] [Algebra R S] {n d : ℕ} (f : PS R n d)
    (a : Fin n → Fin d → S) :
    nv (algebraMap R S) f a = nEval f (fun q : Fin n × Fin d => a q.1 q.2) := by
  unfold nv nEval tEval
  rfl

private lemma sep_nil {R : Type} [CommRing R] {n d : ℕ} (f f' : PS R n d)
    (h : ∀ (S : Type) [CommRing S] [Algebra R S] (a : Fin n → Fin d → S), (∀ i j, IsNilpotent (a i j)) →
      nv (algebraMap R S) f a = nv (algebraMap R S) f' a) : f = f' :=
  GlobalTheory.T.powerSeries_eq_of_evalAtNilpotentPoints_eq R ⊥ inferInstance n d f f' (fun S _ _ _ _ _ a ha => h S a ha)

private lemma nv_ev {R S : Type} [CommRing R] [CommRing S] (s : R →+* S) {n m d : ℕ}
    (a : Fin n → Fin d → S) (ha : ∀ i j, IsNilpotent (a i j)) (b : Fin m → Fin d → PS R n d) (f : PS R m d)
    (hb : ∀ i j, MvPowerSeries.constantCoeff (b i j) = 0) :
    nv s (ev b f) a = nv s f (fun i j => nv s (b i j) a) :=
  (nv_calculus R S s n d a ha).2.2.1 m d b f hb

private lemma nv_X {R S : Type} [CommRing R] [CommRing S] (s : R →+* S) {n d : ℕ}
    (a : Fin n → Fin d → S) (ha : ∀ i j, IsNilpotent (a i j)) (i : Fin n) (j : Fin d) :
    nv s (MvPowerSeries.X (i, j)) a = a i j := by
  obtain ⟨ψ, h1, -, h3⟩ := (nv_calculus R S s n d a ha).1
  rw [← h1, h3]

private lemma nv_zero {R S : Type} [CommRing R] [CommRing S] (s : R →+* S) {n d : ℕ}
    (a : Fin n → Fin d → S) (ha : ∀ i j, IsNilpotent (a i j)) :
    nv s (0 : PS R n d) a = 0 := by
  obtain ⟨ψ, h1, -, -⟩ := (nv_calculus R S s n d a ha).1
  rw [← h1, map_zero]

private lemma nilpotent_eval_subst_pair {R S : Type} [CommRing R] [CommRing S] (s : R →+* S) {n d : ℕ}
    (a : Fin n → Fin d → S) (ha : ∀ i j, IsNilpotent (a i j)) (b c : Fin d → PS R n d) (f : PS R 2 d)
    (hb : ∀ j, MvPowerSeries.constantCoeff (b j) = 0) (hc : ∀ j, MvPowerSeries.constantCoeff (c j) = 0) :
    nv s (ev ![b, c] f) a = nv s f ![fun j => nv s (b j) a, fun j => nv s (c j) a] := by
  rw [nv_ev s a ha _ f (by intro i j; fin_cases i; exacts [hb j, hc j])]
  congr 1
  funext i j
  fin_cases i <;> rfl

private lemma const_pt {R : Type} [CommRing R] {n d : ℕ} (i : Fin n) (j : Fin d) :
    MvPowerSeries.constantCoeff (pt R d i j) = 0 := by
  simp [pt]

private lemma nv_pt {R S : Type} [CommRing R] [CommRing S] (s : R →+* S) {n d : ℕ}
    (a : Fin n → Fin d → S) (ha : ∀ i j, IsNilpotent (a i j)) (i : Fin n) :
    (fun j => nv s (pt R d i j) a) = a i := funext fun j => nv_X s a ha i j

private lemma nv_at_zero {R : Type} [CommRing R] {n d : ℕ} (f : PS R n d) :
    nv (algebraMap R R) f (0 : Fin n → Fin d → R) = MvPowerSeries.constantCoeff f := by
  have := (nv_calculus R R (algebraMap R R) n d 0 (fun _ _ => IsNilpotent.zero)).2.2.2.2.2
    (fun _ _ _ _ => by simp) f
  simpa using this

private lemma constantCoeff_germEvalTwo_eq_zero {R : Type} [CommRing R] {n d : ℕ} (b c : Fin d → PS R n d) (f : PS R 2 d)
    (hb : ∀ j, MvPowerSeries.constantCoeff (b j) = 0) (hc : ∀ j, MvPowerSeries.constantCoeff (c j) = 0)
    (hf : MvPowerSeries.constantCoeff f = 0) :
    MvPowerSeries.constantCoeff (ev ![b, c] f) = 0 := by
  rw [← nv_at_zero, nilpotent_eval_subst_pair _ _ (fun _ _ => IsNilpotent.zero) _ _ _ hb hc, ← hf, ← nv_at_zero]
  congr 1
  funext i j
  fin_cases i
  · exact (nv_at_zero _).trans (hb j)
  · exact (nv_at_zero _).trans (hc j)

theorem exists_nilChart : ∀ (R : Type) [CommRing R] [IsLocalRing R] (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (g : ℕ), SmoothOfRelativeDimension g G.hom → ∃ (F : FGLaw R g) (X : Fam G g), NilChart G F.F X := by
  intro R _ _ G _ _ g hG
  classical
  obtain ⟨x, h0, hnat, hinj, hsur⟩ := GlobalTheory.NilCoord.nilpotent_coordinates G g hG
  have hser := @GlobalTheory.exists_series_of_natural_on_nilpotent (@GlobalTheory.nEval_basic)
  obtain ⟨F0, hF0⟩ := GlobalTheory.ChLaw.groupLaw_powerSeries (@GlobalTheory.nEval_basic) (@hser) G g x ⟨h0, hnat, hinj, hsur⟩
  have hF : ∀ k : Fin g, ∃ f : PS R 2 g, ∀ (S : Type) [CommRing S] [Algebra R S] (u : Fin 2 × Fin g → S),
      (∀ i, IsNilpotent (u i)) → fAdd F0 (fun j => u (0, j)) (fun j => u (1, j)) k = nEval f u := by
    intro k
    refine hser (fun S _ _ u => fAdd F0 (fun j => u (0, j)) (fun j => u (1, j)) k) ?_
    intro S _ _ S' _ _ φ u hu
    unfold fAdd
    rw [((GlobalTheory.nEval_basic (F0 k) S _).2 (by rintro (i | i) <;> exact hu _)).1 S' φ]
    congr 1
    funext i
    rcases i with i | i <;> rfl
  choose F hF using hF
  have hFe : ∀ (S : Type) [CommRing S] [Algebra R S] (a b : Fin g → S), (∀ i, IsNilpotent (a i)) →
      (∀ i, IsNilpotent (b i)) → fAdd F0 a b = fun k => nv (algebraMap R S) (F k) ![a, b] := by
    intro S _ _ a b ha hb
    funext k
    rw [nv_eq_nEval, ← hF k S _ (by rintro ⟨i, j⟩; fin_cases i; exacts [ha j, hb j])]
    rfl
  have law : ∀ (S : Type) [CommRing S] [Algebra R S] (a b : Fin g → S), (∀ i, IsNilpotent (a i)) →
      (∀ i, IsNilpotent (b i)) → x S a * x S b = x S (fun k => nv (algebraMap R S) (F k) ![a, b]) := by
    intro S _ _ a b ha hb
    rw [← hFe S a b ha hb]
    exact (hF0 S a b ha hb).2
  have nil : ∀ (S : Type) [CommRing S] [Algebra R S] (a b : Fin g → S), (∀ i, IsNilpotent (a i)) →
      (∀ i, IsNilpotent (b i)) → ∀ k, IsNilpotent (nv (algebraMap R S) (F k) ![a, b]) := by
    intro S _ _ a b ha hb k
    have h1 := (hF0 S a b ha hb).1 k
    rw [hFe S a b ha hb] at h1
    have h : Ideal.span (Set.range a ∪ Set.range b) ≤ nilradical S := Ideal.span_le.2 (by
      rintro _ (⟨i, rfl⟩ | ⟨i, rfl⟩)
      exacts [mem_nilradical.2 (ha i), mem_nilradical.2 (hb i)])
    exact mem_nilradical.1 (h h1)
  have hz : ∀ (S : Type) [CommRing S] (i : Fin g), IsNilpotent ((0 : Fin g → S) i) :=
    fun S _ i => IsNilpotent.zero
  have unitL : ∀ (S : Type) [CommRing S] [Algebra R S] (a : Fin g → S), (∀ i, IsNilpotent (a i)) →
      (fun k => nv (algebraMap R S) (F k) ![0, a]) = a := by
    intro S _ _ a ha
    refine hinj S _ _ (nil S _ _ (hz S) ha) ha ?_
    rw [← law S _ _ (hz S) ha, h0, _root_.one_mul]
  have const : ∀ k, MvPowerSeries.constantCoeff (F k) = 0 := by
    intro k
    have h := congrFun (unitL R 0 (hz R)) k
    rw [← nv_at_zero]
    refine Eq.trans ?_ h
    congr 1
    funext i j
    fin_cases i <;> rfl
  refine ⟨⟨F, const, ?_, ?_, ?_⟩, x, ⟨h0, hnat, hinj, ?_, law⟩⟩
  · intro k
    refine sep_nil _ _ fun S _ _ a ha => ?_
    rw [nilpotent_eval_subst_pair _ a ha (0 : Fin g → PS R 1 g) _ _ (fun _ => map_zero _) (const_pt _), nv_pt _ a ha, nv_X _ a ha]
    have e : (fun j => nv (algebraMap R S) ((0 : Fin g → PS R 1 g) j) a) = 0 :=
      funext fun j => nv_zero _ a ha
    rw [e]
    exact congrFun (unitL S (a 0) (ha 0)) k
  · intro k
    refine sep_nil _ _ fun S _ _ a ha => ?_
    rw [nilpotent_eval_subst_pair _ a ha _ _ _ (const_pt _) (const_pt _), nv_pt _ a ha, nv_pt _ a ha]
    have e : a = ![a 0, a 1] := by
      funext i
      fin_cases i <;> rfl
    conv_rhs => rw [e]
    refine congrFun (hinj S _ _ (nil S _ _ (ha 1) (ha 0)) (nil S _ _ (ha 0) (ha 1)) ?_) k
    rw [← law S _ _ (ha 1) (ha 0), ← law S _ _ (ha 0) (ha 1), _root_.mul_comm]
  · intro k
    refine sep_nil _ _ fun S _ _ a ha => ?_
    rw [nilpotent_eval_subst_pair _ a ha _ _ _ (fun l => constantCoeff_germEvalTwo_eq_zero _ _ _ (const_pt _) (const_pt _) (const l)) (const_pt _),
      nilpotent_eval_subst_pair _ a ha _ _ _ (const_pt _) (fun l => constantCoeff_germEvalTwo_eq_zero _ _ _ (const_pt _) (const_pt _) (const l))]
    simp only [nilpotent_eval_subst_pair _ a ha _ _ _ (const_pt _) (const_pt _), nv_pt _ a ha]
    refine congrFun (hinj S _ _ (nil S _ _ (nil S _ _ (ha 0) (ha 1)) (ha 2))
      (nil S _ _ (ha 0) (nil S _ _ (ha 1) (ha 2))) ?_) k
    rw [← law S _ _ (nil S _ _ (ha 0) (ha 1)) (ha 2), ← law S _ _ (ha 0) (nil S _ _ (ha 1) (ha 2)),
      ← law S _ _ (ha 0) (ha 1), ← law S _ _ (ha 1) (ha 2), _root_.mul_assoc]
  · intro S _ _ S' _ _ ρ σ hρσ hn z hz'
    refine hsur S S' ρ (fun y => ⟨σ y, AlgHom.congr_fun hρσ y⟩) ?_ z hz'
    intro c hc
    obtain ⟨N, hN⟩ := hn
    have := Ideal.pow_mem_pow hc N
    rw [hN] at this
    exact ⟨N, by simpa using this⟩

end GlobalTheory.ChF
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsPowerSeriesOfNaturalNilpotentPointsStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_powerSeries_of_natural_nilpotentPoints : ∀ (R : Type) [CommRing R] (I : Ideal R), IsAdicComplete I R → ∀ (n d : ℕ) (L : ∀ (S : Type) [CommRing S] [Algebra R S], Prop), (∀ (k m : ℕ), L (Geo.Tor.JetR R (Fin n × Fin d) m ⧸ (I ^ (k + 1)).map (algebraMap R (Geo.Tor.JetR R (Fin n × Fin d) m)))) → ∀ (c : ∀ (S : Type) [CommRing S] [Algebra R S], (Fin n → Fin d → S) → S), (∀ (S : Type) [CommRing S] [Algebra R S] (S' : Type) [CommRing S'] [Algebra R S'] (φ : S →ₐ[R] S') (a : Fin n → Fin d → S), L S → L S' → (∀ y : S, ∃ r : R, IsNilpotent (y - algebraMap R S r)) → (∃ k, Kills I k S) → (∀ i j, IsNilpotent (a i j)) → φ (c S a) = c S' (fun i j => φ (a i j))) → ∃ f : PS R n d, ∀ (S : Type) [CommRing S] [Algebra R S] (a : Fin n → Fin d → S), L S → (∃ k, Kills I k S) → (∀ i j, IsNilpotent (a i j)) → c S a = nv (algebraMap R S) f a := by
  first | exact @GlobalTheory.ChF.exists_series_of_natural | exact GlobalTheory.ChF.exists_series_of_natural | (intros; apply GlobalTheory.ChF.exists_series_of_natural <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.FormalSeriesJacobianChainRuleLinearPartStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formalSeriesJacobian_chain_rule_linearPart : ∀ (R : Type) [CommRing R] (d e : ℕ) (φ : Fin e → PS R 1 d), (∀ j, MvPowerSeries.constantCoeff (φ j) = 0) → (∀ u : PS R 1 e, dl (sub ![φ] u) = (lin φ)ᵀ *ᵥ dl u ∧ MvPowerSeries.constantCoeff (sub ![φ] u) = MvPowerSeries.constantCoeff u) ∧ (∀ (m : ℕ) (ψ : Fin m → PS R 1 e), lin (fun j => sub ![φ] (ψ j)) = lin ψ * lin φ) ∧ ∀ (F : FGLaw R d) (F' : FGLaw R e), IsHomF F.F F'.F φ → ∀ u, IsCh F'.F u → IsCh F.F (sub ![φ] u) := by
  first | exact @GlobalTheory.ChF.chain_rule_lin | exact GlobalTheory.ChF.chain_rule_lin | (intros; apply GlobalTheory.ChF.chain_rule_lin <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.MultiplicativeFormalGroupLawPowerPTorsionFiniteFStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.multiplicativeFormalGroupLawPower_pTorsion_finiteFree : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (r : ℕ), FH p (gmF O r) := by
  first | exact @GlobalTheory.ChF.fh_gmF | exact GlobalTheory.ChF.fh_gmF | (intros; apply GlobalTheory.ChF.fh_gmF <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.NilpotentChartBaseChangeFormalGroupStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nilpotentChart_baseChange_formalGroup : ∀ (R R' : Type) [CommRing R] [CommRing R'] (β : R →+* R') (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (G' : Over (Spec (CommRingCat.of R'))) [GrpObj G'] [IsCommMonObj G'] (π : G'.left ⟶ G.left), Geo.Tor.IsGrpPullback G' G (Spec.map (CommRingCat.ofHom β)) π → ∀ (d : ℕ) (F : Fin d → PS R 2 d) (X : Fam G d), NilChart G F X → ∃ X' : Fam G' d, NilChart G' (fun i => MvPowerSeries.map β (F i)) X' ∧ ∀ (f : G ⟶ G) (f' : G' ⟶ G') (α : Fin d → PS R 1 d), f'.left ≫ π = π ≫ f.left → Reads X X f α → Reads X' X' f' (fun i => MvPowerSeries.map β (α i)) := by
  first | exact @GlobalTheory.ChF.nilChart_baseChange | exact GlobalTheory.ChF.nilChart_baseChange | (intros; apply GlobalTheory.ChF.nilChart_baseChange <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ToricPointExtensionTangentSeqEquivariantStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.toricPointExtension_tangentSeq_equivariant : ∀ (R : Type) [CommRing R] (I : Ideal R) [IsAdicComplete I R] (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (B : Over (Spec (CommRingCat.of R))) [GrpObj B] [IsCommMonObj B] (X : Type) [AddCommGroup X] (E : PtExt I G B X) (d g : ℕ) (F : FGLaw R d) (FB : FGLaw R g) (x : Fam G d) (xB : Fam B g), NilChart G F.F x → NilChart B FB.F xB → ∀ (r : ℕ) (β : Module.Basis (Fin r) ℤ X) (J : Fin d → PS R 1 r) (Q : Fin g → PS R 1 d), (∀ j, MvPowerSeries.constantCoeff (J j) = 0) → (∀ j, MvPowerSeries.constantCoeff (Q j) = 0) → (∀ (S : Type) [CommRing S] [Algebra R S] (h : ∃ k, Kills I k S) (a : Fin d → S), (∀ i, IsNilpotent (a i)) → E.q S h (x S a) = xB S (fun j => nv (algebraMap R S) (Q j) ![a])) → (∀ (S : Type) [CommRing S] [Algebra R S] (h : ∃ k, Kills I k S) (χ : Multiplicative X →* Sˣ) (t : Fin r → S), (∀ i, IsNilpotent (t i)) → (∀ j, (χ (Multiplicative.ofAdd (β j)) : S) = 1 + t j) → E.i S h χ = x S (fun j => nv (algebraMap R S) (J j) ![t])) → ∀ (f : G ⟶ G) (α : Fin d → PS R 1 d), Reads x x f α → (∀ (fB : B ⟶ B) (αB : Fin g → PS R 1 g), Reads xB xB fB αB → (∀ (S : Type) [CommRing S] [Algebra R S] (h : ∃ k, Kills I k S) z, E.q S h (z ≫ f) = E.q S h z ≫ fB) → lin Q * lin α = lin αB * lin Q) ∧ ∀ hm : X →+ X, (∀ (S : Type) [CommRing S] [Algebra R S] (h : ∃ k, Kills I k S) χ χ', (∀ y, χ' (Multiplicative.ofAdd y) = χ (Multiplicative.ofAdd (hm y))) → E.i S h χ ≫ f = E.i S h χ') → lin α * lin J = lin J * Matrix.of (fun i k => ((β.repr (hm (β i)) k : ℤ) : R)) := by
  first | exact @GlobalTheory.ChF.lin_tangentSeq_equivariant | exact GlobalTheory.ChF.lin_tangentSeq_equivariant | (intros; apply GlobalTheory.ChF.lin_tangentSeq_equivariant <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ToricPointExtensionTangentSeqSplitExactStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.toricPointExtension_tangentSeq_splitExact : ∀ (R : Type) [CommRing R] (I : Ideal R) [IsAdicComplete I R] (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (B : Over (Spec (CommRingCat.of R))) [GrpObj B] [IsCommMonObj B] (X : Type) [AddCommGroup X] (E : PtExt I G B X) (d g : ℕ) (F : FGLaw R d) (FB : FGLaw R g) (x : Fam G d) (xB : Fam B g), NilChart G F.F x → NilChart B FB.F xB → ∀ (r : ℕ) (β : Module.Basis (Fin r) ℤ X) (J : Fin d → PS R 1 r) (Q : Fin g → PS R 1 d), (∀ j, MvPowerSeries.constantCoeff (J j) = 0) → (∀ j, MvPowerSeries.constantCoeff (Q j) = 0) → (∀ (S : Type) [CommRing S] [Algebra R S] (h : ∃ k, Kills I k S) (a : Fin d → S), (∀ i, IsNilpotent (a i)) → E.q S h (x S a) = xB S (fun j => nv (algebraMap R S) (Q j) ![a])) → (∀ (S : Type) [CommRing S] [Algebra R S] (h : ∃ k, Kills I k S) (χ : Multiplicative X →* Sˣ) (t : Fin r → S), (∀ i, IsNilpotent (t i)) → (∀ j, (χ (Multiplicative.ofAdd (β j)) : S) = 1 + t j) → E.i S h χ = x S (fun j => nv (algebraMap R S) (J j) ![t])) → SplitEx (lin J) (lin Q) := by
  first | exact @GlobalTheory.ChF.tangent_splitEx | exact GlobalTheory.ChF.tangent_splitEx | (intros; apply GlobalTheory.ChF.tangent_splitEx <;> assumption)
end

