import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.SubThickRees
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.Bundle0001
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSmulSecNonzeroOnSpecialFibre
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0248
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ConstantCoeffSurjective
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.GaloisTwistIdentitySection
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNormalised
import GroundTheory.LocalFields.Bundle0016
import GroundTheory.GlobalFields.LocalFieldAtPlace

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NatCastIsUnit
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Polynomial DividedPowers GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.B

namespace GlobalTheory.CompanionTheory.RootsDivide

theorem nilp_step {B : Type} [CommRing B] (p : ℕ) (hp : p.Prime) (hpn : IsNilpotent (p : B))
    (y : B) (h : IsNilpotent (y ^ p - 1)) : IsNilpotent (y - 1) := by
  obtain ⟨r, hr⟩ := exists_add_pow_prime_eq hp (y - 1) (1 : B)
  have e1 : (y - 1) ^ p = (y ^ p - 1) - (p : B) * ((y - 1) * r) := by
    have : (y - 1 + 1) = y := by ring
    rw [this] at hr
    rw [hr]; simp only [one_pow]; ring
  refine IsNilpotent.of_pow (m := p) ?_
  rw [e1]
  exact (Commute.all _ _).isNilpotent_sub h ((Commute.all _ _).isNilpotent_mul_right hpn)

theorem nilp_all {B : Type} [CommRing B] (p : ℕ) (hp : p.Prime) (e : ℕ → B)
    (hpn : IsNilpotent (p : B)) (he : ∀ k, e (k + 1) ^ p = e k)
    (h0 : IsNilpotent (e 0 - 1)) (k : ℕ) : IsNilpotent (e k - 1) := by
  induction k with
  | zero => exact h0
  | succ k ih => exact nilp_step p hp hpn _ (by rw [he]; exact ih)

theorem pow_tower {B : Type} [CommRing B] (p : ℕ) (e : ℕ → B)
    (he : ∀ k, e (k + 1) ^ p = e k) (k n : ℕ) : e (k + n) ^ (p ^ n) = e k := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', pow_mul, ← add_assoc, he, ih]

theorem natCast_isUnit {B : Type} [CommRing B] (p : ℕ) (hp : p.Prime)
    (hpn : IsNilpotent (p : B)) (c : ℕ) (hc : ¬ p ∣ c) : IsUnit (c : B) := by
  have hcop : IsCoprime (c : ℤ) (p : ℤ) := by
    rw [Nat.isCoprime_iff_coprime]
    exact ((Nat.Prime.coprime_iff_not_dvd hp).2 hc).symm
  obtain ⟨a, b, hab⟩ := hcop
  have h1 : (a : B) * (c : B) + (b : B) * (p : B) = 1 := by
    have := congrArg (Int.cast : ℤ → B) hab
    push_cast at this
    exact this
  have h2 : IsUnit ((a : B) * (c : B)) := by
    have : (a : B) * (c : B) = 1 - (b : B) * (p : B) := by rw [← h1]; ring
    rw [this]
    exact ((Commute.all _ _).isNilpotent_mul_left hpn).isUnit_one_sub
  exact isUnit_of_mul_isUnit_right h2

theorem geom_isUnit {B : Type} [CommRing B] (x : B) (hx : IsNilpotent (x - 1)) (n : ℕ)
    (hn : IsUnit (n : B)) : IsUnit (∑ i ∈ Finset.range n, x ^ i) := by
  have hd : (x - 1) ∣ (∑ i ∈ Finset.range n, x ^ i) - (n : B) := by
    have : (∑ i ∈ Finset.range n, x ^ i) - (n : B) = ∑ i ∈ Finset.range n, (x ^ i - 1) := by
      simp [Finset.sum_sub_distrib]
    rw [this]
    refine Finset.dvd_sum fun i _ => ?_
    simpa using sub_dvd_pow_sub_pow x 1 i
  obtain ⟨t, ht⟩ := hd
  have hnil : IsNilpotent ((∑ i ∈ Finset.range n, x ^ i) - (n : B)) := by
    rw [ht]; exact (Commute.all _ _).isNilpotent_mul_right hx
  have : (∑ i ∈ Finset.range n, x ^ i) = (n : B) + ((∑ i ∈ Finset.range n, x ^ i) - (n : B)) := by
    ring
  rw [this]
  exact hnil.isUnit_add_left_of_commute hn (Commute.all _ _)

theorem sub_one_dvd : ∀ (p : ℕ), p.Prime → ∀ {B : Type} [CommRing B] (e : ℕ → B),
    IsNilpotent (p : B) → (∀ k, e (k + 1) ^ p = e k) → IsNilpotent (e 0 - 1) →
    ∀ m c : ℕ, ¬ p ^ m ∣ c → (e m ^ c - 1) ∣ (e 1 - 1) := by
  intro p hp B _ e hpn he h0 m c hc
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hc (dvd_zero _)
  obtain ⟨j, c', hpc, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hc0 p hp.ne_one
  have hjm : j < m := by
    by_contra hle
    exact hc (Dvd.dvd.mul_right (pow_dvd_pow p (not_lt.1 hle)) c')
  obtain ⟨l, rfl⟩ : ∃ l, m = (l + 1) + j := ⟨m - j - 1, by omega⟩
  set x := e (l + 1) with hxdef
  have hem : e (l + 1 + j) ^ (p ^ j * c') = x ^ c' := by
    rw [pow_mul, pow_tower p e he]
  rw [hem]
  have hxn : IsNilpotent (x - 1) := nilp_all p hp e hpn he h0 _
  have hu : IsUnit (∑ i ∈ Finset.range c', x ^ i) :=
    geom_isUnit x hxn c' (natCast_isUnit p hp hpn c' hpc)
  have hfac : x ^ c' - 1 = (x - 1) * ∑ i ∈ Finset.range c', x ^ i := by
    rw [mul_comm, geom_sum_mul]
  rw [hfac, hu.mul_right_dvd]
  have h1 : x ^ (p ^ l) = e 1 := by
    have := pow_tower p e he 1 l
    rwa [add_comm 1 l] at this
  rw [← h1]
  simpa using sub_dvd_pow_sub_pow x 1 (p ^ l)

end GlobalTheory.CompanionTheory.RootsDivide
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PreimageOpenTopOfJacobsonSurjection
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry Polynomial DividedPowers GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.B

noncomputable section

namespace GlobalTheory.CompanionTheory.SchAtlas

open GlobalTheory.AbLaw GlobalTheory.PrimSec

variable {O : Type} [CommRing O] {X : Scheme.{0}}

def subOf (q : X ⟶ Spec (CommRingCat.of O)) (U : X.Opens) : (schFn q).Sub where
  In {B} y := ⊤ ≤ (show Spec B ⟶ X from y) ⁻¹ᵁ U
  in_map {B B'} φ y h := by
    intro p _
    exact h (show (Spec.map φ p : Spec B) ∈ (⊤ : (Spec B).Opens) from trivial)

theorem fromSpec_comp_cst (q : X ⟶ Spec (CommRingCat.of O)) {W : X.Opens} (hW : IsAffineOpen W) :
    hW.fromSpec ≫ q = Spec.map (CommRingCat.ofHom (cst q W)) := by
  rw [← IsAffineOpen.SpecMap_appLE_fromSpec q (isAffineOpen_top _) hW (fun _ _ => trivial),
    IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp]
  congr 1

theorem small_of_affine (q : X ⟶ Spec (CommRingCat.of O)) (V : (schFn q).Sub) {W : X.Opens}
    (hW : IsAffineOpen W)
    (hV : ∀ {B : CommRingCat.{0}} (y : Spec B ⟶ X), V.In (B := B) y ↔ ⊤ ≤ y ⁻¹ᵁ W)
    {d : ℕ} (T : Fin d → Γ(X, W)ˣ)
    (et : (MvPolynomial.eval₂Hom (cst q W) fun k => (T k : Γ(X, W))).Etale) :
    Nonempty (V.fn.Small d) := by
  refine ⟨{ R := Γ(X, W), a := cst q W, T := T, et := et,
            y₀ := ⟨hW.fromSpec, (hV _).2 hW.fromSpec_preimage_self.ge⟩,
            ov := fromSpec_comp_cst q hW,
            univ := ?_ }⟩
  intro B y f _
  have hy : ⊤ ≤ (show Spec B ⟶ X from y.1) ⁻¹ᵁ W := (hV _).1 y.2
  have hr : Set.range (show Spec B ⟶ X from y.1) ⊆ Set.range hW.fromSpec := by
    rintro _ ⟨p, rfl⟩
    exact hW.range_fromSpec.ge (hy (show p ∈ (⊤ : (Spec B).Opens) from trivial))
  refine ⟨(Spec.preimage (IsOpenImmersion.lift hW.fromSpec (show Spec B ⟶ X from y.1) hr)).hom, ?_, ?_⟩
  · refine Subtype.ext ?_
    exact (congrArg (· ≫ hW.fromSpec) (Spec.map_preimage _)).trans (IsOpenImmersion.lift_fac _ _ _)
  · intro g hg
    have h1 : Spec.map (CommRingCat.ofHom g) ≫ hW.fromSpec = (show Spec B ⟶ X from y.1) :=
      congrArg Subtype.val hg
    have h2 : Spec.map (CommRingCat.ofHom g) =
        IsOpenImmersion.lift hW.fromSpec (show Spec B ⟶ X from y.1) hr := by
      rw [← cancel_mono hW.fromSpec, IsOpenImmersion.lift_fac, h1]
    have h3 := Spec.map_injective (h2.trans (Spec.map_preimage _).symm)
    exact congrArg CommRingCat.Hom.hom h3

theorem rs_etale {U W : X.Opens} (hU : IsAffineOpen U) (hW : IsAffineOpen W) (h : W ≤ U) :
    (rs X h).Etale := by
  have h1 := (𝟙 X : X ⟶ X).etale_appLE hU hW h
  have e : (𝟙 X : X ⟶ X).appLE U W h = X.presheaf.map (homOfLE h).op := by
    simp [Scheme.Hom.appLE]
  rw [e] at h1
  exact h1

theorem et_res (q : X ⟶ Spec (CommRingCat.of O)) {U W : X.Opens} (hU : IsAffineOpen U)
    (hW : IsAffineOpen W) (h : W ≤ U) {d : ℕ} (t : Fin d → Γ(X, U))
    (et : (MvPolynomial.eval₂Hom (cst q U) t).Etale) :
    (MvPolynomial.eval₂Hom (cst q W) fun k => rs X h (t k)).Etale := by
  have e : MvPolynomial.eval₂Hom (cst q W) (fun k => rs X h (t k)) =
      (rs X h).comp (MvPolynomial.eval₂Hom (cst q U) t) := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) fun k => ?_
    · simp [rs_cst]
    · simp
  rw [e]
  exact RingHom.Etale.stableUnderComposition _ _ et (rs_etale hU hW h)

theorem et_shift {R : Type} [CommRing R] (a : O →+* R) {d : ℕ} (t : Fin d → R) (e : Fin d → O)
    (et : (MvPolynomial.eval₂Hom a t).Etale) :
    (MvPolynomial.eval₂Hom a fun k => t k + a (e k)).Etale := by
  let σ : MvPolynomial (Fin d) O →+* MvPolynomial (Fin d) O :=
    MvPolynomial.eval₂Hom MvPolynomial.C fun k => MvPolynomial.X k + MvPolynomial.C (e k)
  let σ' : MvPolynomial (Fin d) O →+* MvPolynomial (Fin d) O :=
    MvPolynomial.eval₂Hom MvPolynomial.C fun k => MvPolynomial.X k - MvPolynomial.C (e k)
  have h1 : σ.comp σ' = RingHom.id _ := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) fun k => ?_ <;> simp [σ, σ']
  have h2 : σ'.comp σ = RingHom.id _ := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) fun k => ?_ <;> simp [σ, σ']
  have hb : Function.Bijective σ := Function.bijective_iff_has_inverse.2
    ⟨σ', fun x => RingHom.congr_fun h2 x, fun x => RingHom.congr_fun h1 x⟩
  have e1 : MvPolynomial.eval₂Hom a (fun k => t k + a (e k)) =
      (MvPolynomial.eval₂Hom a t).comp σ := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) fun k => ?_ <;> simp [σ]
  rw [e1]
  exact RingHom.Etale.stableUnderComposition _ _ (RingHom.Etale.of_bijective hb) et

theorem exists_unit_chart (q : X ⟶ Spec (CommRingCat.of O)) [Smooth q] (x : X) :
    ∃ U : X.Opens, IsAffineOpen U ∧ x ∈ U ∧ ∃ (n : ℕ) (T : Fin n → Γ(X, U)ˣ),
      (MvPolynomial.eval₂Hom (cst q U) fun k => (T k : Γ(X, U))).Etale := by
  classical
  obtain ⟨V, hV, hx, -, n, φ, hφC, hφ⟩ := exists_etale_chart q (U := ⊤) (x := x) trivial
  let t : Fin n → Γ(X, V) := fun k => φ (MvPolynomial.X k)
  have e0 : φ = MvPolynomial.eval₂Hom (cst q V) t := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) fun k => ?_
    · simpa using RingHom.congr_fun hφC r
    · simp [t]
  rw [e0] at hφ
  let P : Ideal Γ(X, V) := (hV.primeIdealOf ⟨x, hx⟩).asIdeal
  have hP : P.IsPrime := (hV.primeIdealOf ⟨x, hx⟩).isPrime
  have hc : ∀ k, ∃ e : O, t k + cst q V e ∉ P := by
    intro k
    by_cases h : t k ∈ P
    · refine ⟨1, fun h' => hP.ne_top ((Ideal.eq_top_iff_one _).2 ?_)⟩
      have := P.sub_mem h' h
      simpa using this
    · exact ⟨0, by simpa using h⟩
  choose e he using hc
  have et := et_shift (cst q V) t e hφ
  let t' : Fin n → Γ(X, V) := fun k => t k + cst q V (e k)
  let h : Γ(X, V) := ∏ k, t' k
  have hh : h ∉ P := by
    intro hm
    obtain ⟨k, -, hk⟩ := (hP.prod_mem_iff).1 hm
    exact he k hk
  have hxW : x ∈ X.basicOpen h := (mem_basicOpen_iff hV ⟨x, hx⟩ h).2 hh
  have hle : X.basicOpen h ≤ V := X.basicOpen_le h
  have hW := hV.basicOpen h
  have hunit : IsUnit (rs X hle h) := RingedSpace.isUnit_res_basicOpen _ h
  have hu : ∀ k, IsUnit (rs X hle (t' k)) := fun k =>
    isUnit_of_dvd_unit (map_dvd (rs X hle) (Finset.dvd_prod_of_mem _ (Finset.mem_univ k))) hunit
  exact ⟨X.basicOpen h, hW, hxW, n, fun k => (hu k).unit, et_res q hV hW hle t' et⟩

theorem exists_unimodular_cover_refining_opens {A : Type} (U : A → X.Opens) (hU : ∀ x : X, ∃ α, x ∈ U α) {B : CommRingCat.{0}}
    (y : Spec B ⟶ X) : ∃ (m : ℕ) (s : Fin m → B), Ideal.span (Set.range s) = ⊤ ∧
      ∀ k (B' : CommRingCat.{0}) (φ : B ⟶ B'), IsUnit (φ.hom (s k)) →
        ∃ α, ⊤ ≤ (Spec.map φ ≫ y) ⁻¹ᵁ U α := by
  classical
  let S : Set B := {s | ∃ α, ∀ p : PrimeSpectrum B, s ∉ p.asIdeal → y p ∈ U α}
  have hS : Ideal.span S = ⊤ := by
    by_contra hne
    obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
    let p : PrimeSpectrum B := ⟨M, hM.isPrime⟩
    obtain ⟨α, hα⟩ := hU (y p)
    have hop : IsOpen {p : PrimeSpectrum B | y p ∈ U α} := (y ⁻¹ᵁ U α).isOpen
    obtain ⟨_, ⟨r, rfl⟩, hpr, hsub⟩ := PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
      (show p ∈ {p : PrimeSpectrum B | y p ∈ U α} from hα) hop
    have hr : r ∈ S := ⟨α, fun p' hp' => hsub hp'⟩
    exact hpr (hle (Ideal.subset_span hr))
  obtain ⟨s', hs', hspan⟩ := (Ideal.span_eq_top_iff_finite S).1 hS
  refine ⟨s'.card, fun k => (s'.equivFin.symm k).1, ?_, ?_⟩
  · have : Set.range (fun k => (s'.equivFin.symm k).1) = (s' : Set B) := by
      ext b
      constructor
      · rintro ⟨k, rfl⟩
        exact (s'.equivFin.symm k).2
      · intro hb
        exact ⟨s'.equivFin ⟨b, hb⟩, by simp⟩
    rw [this, hspan]
  · intro k B' φ hu
    obtain ⟨α, hα⟩ := hs' (s'.equivFin.symm k).2
    refine ⟨α, fun p' _ => ?_⟩
    have h1 : (s'.equivFin.symm k).1 ∉ (PrimeSpectrum.comap φ.hom p').asIdeal := fun hm =>
      (p' : PrimeSpectrum B').isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hm hu)
    exact hα _ h1

theorem preimage_open_top_of_jacobson_surjection (U : X.Opens) (B B' : CommRingCat.{0}) (φ : B ⟶ B') (y : Spec B ⟶ X)
    (hs : Function.Surjective φ.hom) (hk : RingHom.ker φ.hom ≤ (⊥ : Ideal B).jacobson)
    (h : ⊤ ≤ (Spec.map φ ≫ y) ⁻¹ᵁ U) : ⊤ ≤ y ⁻¹ᵁ U := by
  intro p _
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal (p : PrimeSpectrum B).asIdeal (p : PrimeSpectrum B).isPrime.ne_top
  let m : PrimeSpectrum B := ⟨M, hM.isPrime⟩
  have hker : RingHom.ker φ.hom ≤ M := hk.trans (sInf_le ⟨bot_le, hM⟩)
  haveI := hM.isPrime
  let m' : PrimeSpectrum B' := ⟨M.map φ.hom, Ideal.map_isPrime_of_surjective hs hker⟩
  have hm' : PrimeSpectrum.comap φ.hom m' = m := by
    refine PrimeSpectrum.ext ?_
    change Ideal.comap φ.hom (M.map φ.hom) = M
    rw [Ideal.comap_map_of_surjective' _ hs, sup_eq_left]
    exact hker
  have h1 : y m ∈ U := by
    have := h (show (m' : Spec B') ∈ (⊤ : (Spec B').Opens) from trivial)
    rw [← hm']
    exact this
  exact ((PrimeSpectrum.le_iff_specializes _ _).mp hle).mem_open (y ⁻¹ᵁ U).isOpen h1

theorem mem_biInf_of_finite {A : Type} [Finite A] (S : Set A) (U : A → X.Opens) {x : X}
    (h : ∀ β ∈ S, x ∈ U β) : x ∈ ⨅ β ∈ S, U β := by
  let G : X.Opens := ⟨⋂ β ∈ S, (U β : Set X), S.toFinite.isOpen_biInter fun β _ => (U β).isOpen⟩
  have hG : G ≤ ⨅ β ∈ S, U β :=
    le_iInf₂ fun β hβ y hy => Set.mem_iInter₂.1 hy β hβ
  exact hG (Set.mem_iInter₂.2 h)

theorem exists_atlas {O : Type} [CommRing O] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of O))
    [Smooth q] [IsSeparated q] [QuasiCompact q] : ∃ d, Nonempty ((schFn q).Atlas d) := by
  classical
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace q
  haveI : X.IsSeparated := by
    rw [Scheme.isSeparated_iff, ← Limits.terminal.comp_from q]
    infer_instance
  choose U hU hx n T et using exists_unit_chart q
  obtain ⟨t, ht⟩ := isCompact_univ.elim_nhds_subcover (fun x => (U x : Set X))
    (fun x _ => (U x).isOpen.mem_nhds (hx x))
  have hcov : ∀ x : X, ∃ α : {x // x ∈ t}, x ∈ U α.1 := by
    intro x
    have := ht.2 (Set.mem_univ x)
    simp only [Set.mem_iUnion] at this
    obtain ⟨a, ha, hxa⟩ := this
    exact ⟨⟨a, ha⟩, hxa⟩
  refine ⟨t.sup n, ⟨⟨{x // x ∈ t}, inferInstance, fun α => subOf q (U α.1),
    fun B y => ?_, fun α B B' φ y hs hk h => ?_, fun S hS => ?_⟩⟩⟩
  · exact exists_unimodular_cover_refining_opens (fun α : {x // x ∈ t} => U α.1) hcov y
  · exact preimage_open_top_of_jacobson_surjection (U α.1) B B' φ y hs hk h
  · obtain ⟨α, hα⟩ := hS
    have hW : IsAffineOpen (⨅ β ∈ S, U (Subtype.val β)) :=
      IsAffineOpen.biInf S S.toFinite ⟨α, hα⟩ fun i _ => hU i.1
    have hle : (⨅ β ∈ S, U (Subtype.val β)) ≤ U α.1 := iInf₂_le α hα
    refine ⟨n α.1, Finset.le_sup α.2, ?_⟩
    refine small_of_affine q _ hW ?_ (fun k => Units.map (rs X hle).toMonoidHom (T α.1 k))
      (et_res q (hU α.1) hW hle _ (et α.1))
    intro B y
    change (∀ β ∈ S, ⊤ ≤ y ⁻¹ᵁ U β.1) ↔ _
    constructor
    · intro h p _
      exact mem_biInf_of_finite S (fun β : {x // x ∈ t} => U β.1)
        fun β hβ => h β hβ (show p ∈ (⊤ : (Spec B).Opens) from trivial)
    · intro h β hβ p hp
      exact (iInf₂_le (f := fun (β : {x // x ∈ t}) (_ : β ∈ S) => U β.1) β hβ) (h hp)

end GlobalTheory.CompanionTheory.SchAtlas
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubSubSmulEqZeroOfSmulEqZero
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Polynomial DividedPowers GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.B

namespace GlobalTheory.CompanionTheory.TwistedUnit

theorem sub_sub_smul_eq_zero_of_smul_eq_zero {Λ N : Type} [CommRing Λ] [AddCommGroup N]
    [Module Λ N] [Module.Flat Λ N] (γ : N →ₗ[Λ] N) (c μ : Λ)
    (h : ∀ x, ∃ x', γ x - x - c • x = μ • x') (z : N) (hz : μ • z = 0) :
    γ z - z - c • z = 0 := by
  obtain ⟨k, a, y, hx, hf⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero (R := Λ) (M := N)
    (f := fun _ : Fin 1 => μ) (x := fun _ : Fin 1 => z) (by simpa using hz)
  choose d hd using h
  have hz' : z = ∑ j, a 0 j • y j := hx 0
  have h0 : ∀ j, μ * a 0 j = 0 := fun j => by simpa using hf j
  have hlin : ∀ j, a 0 j • (γ (y j) - y j - c • y j) = 0 := by
    intro j
    rw [hd, smul_smul, mul_comm, h0, zero_smul]
  have hsum : γ z - z - c • z = ∑ j, a 0 j • (γ (y j) - y j - c • y j) := by
    conv_lhs => rw [hz']
    simp only [map_sum, map_smul, Finset.smul_sum, smul_sub, Finset.sum_sub_distrib]
    congr 1
    exact Finset.sum_congr rfl (fun j _ => smul_comm _ _ _)
  rw [hsum]
  exact Finset.sum_eq_zero (fun j _ => hlin j)

theorem smul_eq_zero_of_fixed {Λ N : Type} [CommRing Λ] [AddCommGroup N] [Module Λ N]
    [Module.Flat Λ N] (γ : N →ₗ[Λ] N) (c w ξ μ : Λ) (hμ : μ = c * w * ξ) (hξ : IsNilpotent ξ)
    (h : ∀ x, ∃ x', γ x - x - c • x = μ • x') (x : N) (hx : γ x = x) : μ • x = 0 := by
  have hE := sub_sub_smul_eq_zero_of_smul_eq_zero γ c μ h
  have R : ∀ n : ℕ, ∀ x, (w * ξ) • (γ x - x) = 0 → ∃ u, μ • (x - ξ ^ n • u) = 0 := by
    intro n
    induction n with
    | zero => exact fun x _ => ⟨x, by simp⟩
    | succ n ih =>
      intro x hx
      obtain ⟨x', hx'⟩ := h x
      have h1 : μ • (x + (w * ξ) • x') = 0 := by
        have : μ • (x + (w * ξ) • x') = (w * ξ) • (γ x - x) := by
          subst hμ
          linear_combination (norm := module) -(w * ξ) • hx'
        rw [this, hx]
      have h2 := hE _ h1
      simp only [map_add, map_smul] at h2
      have hM : (w * ξ) • (γ x' - x') = 0 := by
        subst hμ
        linear_combination (norm := module) h2 - hx'
      obtain ⟨u, hu⟩ := ih x' hM
      refine ⟨-w • u, ?_⟩
      have : μ • (x - ξ ^ (n + 1) • (-w • u))
          = μ • (x + (w * ξ) • x') - (w * ξ) • (μ • (x' - ξ ^ n • u)) := by
        module
      rw [this, h1, hu]
      simp
  obtain ⟨n, hn⟩ := hξ
  obtain ⟨u, hu⟩ := R n x (by simp [hx])
  simpa [hn] using hu

theorem exists_mem_smul_top {Λ N : Type} [CommRing Λ] [AddCommGroup N] [Module Λ N]
    (γ : N →ₗ[Λ] N) (c μ : Λ) (h : ∀ x, ∃ x', γ x - x - c • x = μ • x') (𝔞 : Ideal Λ) (x : N)
    (hx : x ∈ 𝔞 • (⊤ : Submodule Λ N)) :
    ∃ x₁ ∈ 𝔞 • (⊤ : Submodule Λ N), γ x - x - c • x = μ • x₁ := by
  induction hx using Submodule.smul_induction_on' with
  | smul a ha n hn =>
    obtain ⟨n', hn'⟩ := h n
    refine ⟨a • n', Submodule.smul_mem_smul ha trivial, ?_⟩
    rw [map_smul]
    linear_combination (norm := module) a • hn'
  | add x hx y hy ihx ihy =>
    obtain ⟨x₁, hx₁, e₁⟩ := ihx
    obtain ⟨y₁, hy₁, e₂⟩ := ihy
    refine ⟨x₁ + y₁, Submodule.add_mem _ hx₁ hy₁, ?_⟩
    rw [map_add]
    linear_combination (norm := module) e₁ + e₂

theorem exists_sub_eq_smul {Λ N : Type} [CommRing Λ] [AddCommGroup N] [Module Λ N]
    (γ : N →ₗ[Λ] N) (c w ξ μ : Λ) (hμ : μ = c * w * ξ) (hξ : IsNilpotent ξ)
    (h : ∀ x, ∃ x', γ x - x - c • x = μ • x') (𝔞 : Ideal Λ) (x : N)
    (hx : x ∈ 𝔞 • (⊤ : Submodule Λ N)) :
    ∃ y ∈ (Ideal.span {ξ} * 𝔞) • (⊤ : Submodule Λ N), γ y - y = μ • x := by
  obtain ⟨n, hn⟩ := hξ
  have P : ∀ m k : ℕ, m + k = n → ∀ x ∈ 𝔞 • (⊤ : Submodule Λ N),
      ∃ y ∈ (Ideal.span {ξ} * 𝔞) • (⊤ : Submodule Λ N), γ y - y = (μ * ξ ^ k) • x := by
    intro m
    induction m with
    | zero =>
      intro k hk x _
      have : ξ ^ k = 0 := by
        rw [show k = n by omega, hn]
      exact ⟨0, Submodule.zero_mem _, by simp [this]⟩
    | succ m ih =>
      intro k hk x hx
      obtain ⟨x₁, hx₁, e⟩ := exists_mem_smul_top γ c μ h 𝔞 x hx
      obtain ⟨y', hy', e'⟩ := ih (k + 1) (by omega) (w • x₁)
        (Submodule.smul_of_tower_mem _ w hx₁)
      have hξx : ξ • x ∈ (Ideal.span {ξ} * 𝔞) • (⊤ : Submodule Λ N) := by
        rw [Submodule.mul_smul]
        exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self ξ) hx
      refine ⟨(w * ξ ^ k) • (ξ • x) - y',
        Submodule.sub_mem _ (Submodule.smul_of_tower_mem _ _ hξx) hy', ?_⟩
      simp only [map_sub, map_smul]
      subst hμ
      linear_combination (norm := module) (w * ξ ^ (k + 1)) • e - e'
  simpa using P n 0 rfl x hx

theorem twisted_bijective_up_to :
    ∀ {Λ N : Type} [CommRing Λ] [AddCommGroup N] [Module Λ N] [Module.Flat Λ N]
      (γ : N →ₗ[Λ] N) (c w ξ μ : Λ), μ = c * w * ξ → IsNilpotent ξ →
      (∀ x, ∃ x', γ x - x - c • x = μ • x') →
      (∀ x, γ x = x → μ • x = 0) ∧ ∀ (𝔞 : Ideal Λ), ∀ x ∈ 𝔞 • (⊤ : Submodule Λ N),
        ∃ y ∈ (Ideal.span {ξ} * 𝔞) • (⊤ : Submodule Λ N), γ y - y = μ • x := by
  intro Λ N _ _ _ _ γ c w ξ μ hμ hξ h
  exact ⟨smul_eq_zero_of_fixed γ c w ξ μ hμ hξ h,
    fun 𝔞 x hx => exists_sub_eq_smul γ c w ξ μ hμ hξ h 𝔞 x hx⟩

end GlobalTheory.CompanionTheory.TwistedUnit
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubThickOnto
section
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry Polynomial DividedPowers GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.B

namespace GlobalTheory.CompanionTheory.ThickSub

theorem subThick_onto {O : Type} [CommRing O] {F : Fn O} (V : F.Sub) (b : Base) (ht : b.t = 1)
    (κ : O →+* b.R ⧸ b.I) : Onto (subThick V b ht κ) fun T => V.In T.y.1.2 := by
  refine ⟨⟨fun {T T'} f => ⟨{
      φ := f.φ, u := f.u, comm := f.comm, dp := f.dp, hle := f.hle,
      pt := Subtype.ext (Prod.ext (congrArg (fun z => z.1.1) f.pt)
        (Subtype.ext (congrArg (fun z => z.1.2) f.pt))),
      hx := fun j => j.elim, hs := f.hs, hv := fun j => j.elim }, rfl⟩⟩,
    ⟨fun {T T'} f g h => Thick.Hom.ext (congrArg (fun m => m.φ) h) (funext fun j => j.elim)⟩,
    fun T => T.y.1.2.2, fun T h => ?_⟩
  refine ⟨{ B := T.B, i := T.i, J := T.J, δ := T.δ, adm := T.adm, compat := T.compat, α := (),
            y := ⟨(T.y.1.1, ⟨T.y.1.2, h⟩), T.y.2⟩, inα := trivial, w := T.w, x := T.x, v := T.v, s := T.s,
            hx := fun j => j.elim, hs := T.hs, hv := T.hv }, ⟨eqToIso rfl⟩⟩

end GlobalTheory.CompanionTheory.ThickSub
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TensorLiftSurjectiveKernelLevelStatement
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensor_lift_surjective_kernel_level : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l) (n : ℕ), Function.Surjective (Algebra.TensorProduct.lift (IsScalarTower.toAlgHom (Ainf l) (Acris l) (A.Acr n)) (IsScalarTower.toAlgHom (Ainf l) A.W (A.Acr n)) (fun _ _ => Commute.all _ _)) ∧ ∀ z : TensorProduct (Ainf l) (Acris l) A.W, Algebra.TensorProduct.lift (IsScalarTower.toAlgHom (Ainf l) (Acris l) (A.Acr n)) (IsScalarTower.toAlgHom (Ainf l) A.W (A.Acr n)) (fun _ _ => Commute.all _ _) z = 0 ↔ z ∈ Ideal.span {(l : TensorProduct (Ainf l) (Acris l) A.W) ^ n} := by
  first | exact @GlobalTheory.CompanionTheory.PerfFil.tens_base_change | exact GlobalTheory.CompanionTheory.PerfFil.tens_base_change | (intros; apply GlobalTheory.CompanionTheory.PerfFil.tens_base_change <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformizerRatioValuationZeroStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformizer_ratio_valuation_zero : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (ϖ ϖ' : 𝓞 F), ϖ ∈ v.asIdeal → ϖ ∉ v.asIdeal ^ 2 → ϖ' ∈ v.asIdeal → ϖ' ∉ v.asIdeal ^ 2 → ∀ U : (v.adicCompletion F)ˣ, (U : v.adicCompletion F) * algebraMap F (v.adicCompletion F) (ϖ : F) = algebraMap F (v.adicCompletion F) (ϖ' : F) → GroundTheory.LocalField.ord (U : v.adicCompletion F) = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Uniformiser.ord_ratio_eq_zero | exact GlobalTheory.CompanionTheory.Uniformiser.ord_ratio_eq_zero | (intros; apply GlobalTheory.CompanionTheory.Uniformiser.ord_ratio_eq_zero <;> assumption)
end

