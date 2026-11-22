import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.CompatH
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.Bundle0004
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SplittingFieldLattices.BasisB
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0156
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0259
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0154
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0151
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0172
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0282
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0180
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.RedGalBase
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PlaneSupports.PlaneSupp
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianPlaneStrongApprox
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0268
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsOfConjEq
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0288
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0262

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OmMorImg
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B

universe w w' v u v' u'

namespace GlobalTheory.CompanionTheory.CrisFil

section General

variable {R R' : Type} [CommRing R] [CommRing R'] {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C']
  {F : C ⥤ ModuleCat.{w} R} {F' : C' ⥤ ModuleCat.{w'} R'} {σ : R →+* R'}

def subMor (m : CH.Mor F F' σ) (S : CH.SubF F) (S' : CH.SubF F')
    (h : ∀ (T : C') (x : F.obj (m.G.obj T)), x ∈ S.S (m.G.obj T) → m.τ T x ∈ S'.S T) :
    CH.Mor S.fn S'.fn σ where
  G := m.G
  τ T := ((m.τ T).domRestrict (S.S (m.G.obj T))).codRestrict (S'.S T) fun x => h T x.1 x.2
  nat φ x := Subtype.ext (m.nat φ x.1)

theorem pull_inc (m : CH.Mor F F' σ) (S : CH.SubF F) (S' : CH.SubF F')
    (h : ∀ (T : C') (x : F.obj (m.G.obj T)), x ∈ S.S (m.G.obj T) → m.τ T x ∈ S'.S T) (n : ℕ) (y : CH.H S.fn n) :
    m.pull n (S.inc.pull n y) = S'.inc.pull n ((subMor m S S' h).pull n y) := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  rfl

theorem pull_img (m : CH.Mor F F' σ) (S : CH.SubF F) (S' : CH.SubF F')
    (h : ∀ (T : C') (x : F.obj (m.G.obj T)), x ∈ S.S (m.G.obj T) → m.τ T x ∈ S'.S T) (n : ℕ) (x : CH.H F n)
    (hx : x ∈ S.img n) : m.pull n x ∈ S'.img n := by
  obtain ⟨y, rfl⟩ := hx
  exact ⟨(subMor m S S' h).pull n y, (pull_inc m S S' h n y).symm⟩

end General

section Thick

variable {b b' : Base} {L : b.Fun} {L' : b'.Fun} {σ : b.R →+* b'.R}

theorem pdPow_obj (m : GlobalTheory.LogCris.Mor L L' σ) (T : Thick L') (r : ℕ) : (m.obj T).pdPow r = T.pdPow r := rfl

variable {Λ Λ' : Type} [CommRing Λ] [CommRing Λ'] {c : Λ →+* b.R} {c' : Λ' →+* b'.R}

theorem omMor_img (m : GlobalTheory.LogCris.Mor L L' σ) (σ₀ : Λ →+* Λ') (h : ∀ a, σ (c a) = c' (σ₀ a)) (r j : ℕ)
    (x : CH.H (OM L c) j) (hx : x ∈ (pdS L c r).img j) : (omMor m σ₀ h).pull j x ∈ (pdS L' c' r).img j :=
  pull_img (omMor m σ₀ h) (pdS L c r) (pdS L' c' r) (fun _ _ hz => hz) j x hx

end Thick

theorem red_fil : ∀ {l : ℕ} [Fact l.Prime], ∀ {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l) (k : Bool) {m n : ℕ} (h : n ≤ m)
    (r j : ℕ), ∀ x ∈ HcFil F κ k m r j, redHc F κ k h j x ∈ HcFil F κ k n r j := by
  intro l _ O _ F κ k m n h r j x hx
  exact omMor_img _ _ _ r j x hx

end GlobalTheory.CompanionTheory.CrisFil
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PdPBotPos
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.BcLoc

theorem dividedPowerFiltration_dividedPowersBot' (O : Type) [CommRing O] {r : ℕ} (hr : r ≠ 0) : pdP (dividedPowersBot O) r = ⊥ := by
  classical
  rw [eq_bot_iff]
  refine Ideal.span_le.2 ?_
  rintro _ ⟨l, hl, hs, rfl⟩
  have hq : ∃ q ∈ l, q.1 ≠ 0 := by
    by_contra h
    push_neg at h
    have : (l.map Prod.fst).sum = 0 := List.sum_eq_zero (by
      intro x hx
      obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hx
      exact h q hq)
    omega
  obtain ⟨q, hq, h0⟩ := hq
  refine List.prod_eq_zero (List.mem_map.2 ⟨q, hq, ?_⟩)
  rw [dividedPowersBot_dpow_eq]
  simp [h0]

section Sq
variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {F : C ⥤ CommAlgCat.{0} R}

theorem sub_of_bot (a b : IdF F) (T : C) (h : a.S T = ⊥) : Subsingleton (sqM a b T) := by
  refine ⟨fun x y => Subtype.ext ?_⟩
  have hx := x.2
  have hy := y.2
  simp only [sqM, h, Ideal.map_bot] at hx hy
  exact (show (x.1 : F.obj T ⧸ b.S T) = 0 from hx).trans (show (y.1 : F.obj T ⧸ b.S T) = 0 from hy).symm

theorem sub_of_top (a b : IdF F) (T : C) (h : b.S T = ⊤) : Subsingleton (sqM a b T) := by
  haveI : Subsingleton (F.obj T ⧸ b.S T) := Ideal.Quotient.subsingleton_iff.2 h
  exact ⟨fun x y => Subtype.ext (Subsingleton.elim _ _)⟩

theorem pi_ex (a b : IdF F) (T : C) {Y : Type} [CommRing Y] {P Q : Ideal Y} (e : Y ≃+* F.obj T)
    (hP : ∀ z, e z ∈ a.S T ↔ z ∈ P) (hQ : ∀ z, e z ∈ b.S T ↔ z ∈ Q) :
    ∃ π : P →+ sqM a b T, Function.Surjective π ∧ (∀ x, π x = 0 ↔ x.1 ∈ Q) ∧
      ∀ x, (π x).1 = Ideal.Quotient.mk _ (e x.1) := by
  refine ⟨AddMonoidHom.mk' (fun x => ⟨Ideal.Quotient.mk _ (e x.1), Ideal.mem_map_of_mem _ ((hP _).2 x.2)⟩)
    (fun x y => Subtype.ext (by simp)), ?_, fun x => ?_, fun x => rfl⟩
  · rintro ⟨y, hy⟩
    obtain ⟨w, hw, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 hy
    refine ⟨⟨e.symm w, (hP _).1 (by simpa using hw)⟩, Subtype.ext ?_⟩
    simp
  · rw [← hQ, ← Ideal.Quotient.eq_zero_iff_mem]
    exact Subtype.ext_iff

theorem theta_ex {G : Type} [CommRing G] [Algebra R G] (a b : IdF F) (T : C) (ht : a.S T = ⊤) (hb : b.S T = ⊥)
    (e : R ⊗[R] G ≃+* F.obj T) (he : ∀ r, e (r ⊗ₜ 1) = algebraMap R (F.obj T) r) :
    ∃ θ : G ≃ₗ[R] sqM a b T, ∀ x, (θ x).1 = Ideal.Quotient.mk _ (e (1 ⊗ₜ x)) := by
  let f : G →ₗ[R] sqM a b T :=
    { toFun := fun x => ⟨Ideal.Quotient.mk _ (e (1 ⊗ₜ x)), Ideal.mem_map_of_mem _ (by rw [ht]; trivial)⟩
      map_add' := fun x y => Subtype.ext (by simp [TensorProduct.tmul_add])
      map_smul' := fun r x => Subtype.ext (by
        have h1 : (1 : R) ⊗ₜ[R] (r • x) = (r ⊗ₜ[R] (1 : G)) * ((1 : R) ⊗ₜ[R] x) := by
          rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one, TensorProduct.tmul_smul,
            TensorProduct.smul_tmul', smul_eq_mul, mul_one]
        change Ideal.Quotient.mk _ (e ((1 : R) ⊗ₜ[R] (r • x))) = r • Ideal.Quotient.mk _ (e ((1 : R) ⊗ₜ[R] x))
        rw [h1, map_mul, he, map_mul, Algebra.smul_def]
        rfl) }
  refine ⟨LinearEquiv.ofBijective f ⟨fun x y h => ?_, ?_⟩, fun x => rfl⟩
  · have h1 := congrArg Subtype.val h
    have h2 := Ideal.Quotient.eq.1 h1
    rw [hb, Ideal.mem_bot, ← map_sub, map_eq_zero_iff _ e.injective, ← TensorProduct.tmul_sub] at h2
    have h3 := congrArg (TensorProduct.lid R G) h2
    simpa [sub_eq_zero] using h3
  · rintro ⟨y, hy⟩
    obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective y
    refine ⟨TensorProduct.lid R G (e.symm w), Subtype.ext ?_⟩
    change Ideal.Quotient.mk _ (e ((1 : R) ⊗ₜ[R] TensorProduct.lid R G (e.symm w))) = _
    have : (1 : R) ⊗ₜ[R] TensorProduct.lid R G (e.symm w) = e.symm w := by
      refine TensorProduct.induction_on (e.symm w) (by simp) (fun r x => ?_) (fun u v hu hv => ?_)
      · simp [TensorProduct.tmul_smul, TensorProduct.smul_tmul']
      · simp only [map_add, TensorProduct.tmul_add, hu, hv]
    rw [this, e.apply_symm_apply]

end Sq

theorem crit_of {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {Φ : PDF R C} (P : Poly Φ)
    {F a : ℤ → IdF Φ.A} {r r₀ : ℤ} (h : P.Crit F r₀) (h0 : a r = F r₀)
    (hk : ∀ k : ℕ, a (r - k) = F (r₀ - k)) : P.Crit a r := by
  intro T b
  rw [h0]
  simp only [hk]
  exact h T b

theorem chart_tens : ∀ {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {I : Ideal A} (γ : DividedPowers I) (l s m : ℕ)
    (S : GrSplit O γ m) {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of O)) {V : X.Opens} {d : ℕ} (cV : Coord q V d),
    letI := (strV q V).toAlgebra
    ∀ (cO : Chart (dividedPowersBot O) 0 q (Ideal.Quotient.mk ⊥) V d) (cA : Chart γ 0 q (κA O I) V d)
      (eO : O ⊗[O] Γ(X, V) ≃+* cO.D.B) (eA : A ⊗[O] Γ(X, V) ≃+* cA.D.B)
      (hD : TO q l s {V} cO.D) (hD' : TS γ q l s {V} cA.D)
      (e : (⟨cO.D, hD⟩ : (TO q l s {V}).FullSubcategory) ⟶ (smO γ q l s {V}).G.obj ⟨cA.D, hD'⟩),
      (∀ r, eO (r ⊗ₜ 1) = cO.D.i r) → (∀ r, eA (r ⊗ₜ 1) = cA.D.i r) →
      (∀ f, e.hom.φ (eO (1 ⊗ₜ f)) = eA (1 ⊗ₜ f)) →
      ∀ (c t : ℤ), 0 ≤ c →
      ∀ (ha : ∀ (i : Fin m) n, (smO γ q l s {V}).LeC (S.ν i n) (sFil _ (t - c - i)) (sFil _ (t - c)))
        (hb : ∀ (i : Fin m) n, (smO γ q l s {V}).LeC (S.ν i n) (sFil _ (t - i)) (sFil _ t)),
      Tens O (N := S.N) (M := fun i => (sq (sFil (TO q l s {V}) (t - c - i)) (sFil (TO q l s {V}) (t - i))).obj ⟨cO.D, hD⟩)
        (M' := (sq (sFil (TS γ q l s {V}) (t - c)) (sFil (TS γ q l s {V}) t)).obj ⟨cA.D, hD'⟩)
        fun i n x => ((smO γ q l s {V}).sqC (S.ν i n) (ha i n) (hb i n)).τ ⟨cA.D, hD'⟩
          (((sq (sFil (TO q l s {V}) (t - c - i)) (sFil (TO q l s {V}) (t - i))).map e).hom x) := by
  intro O A _ _ _ I γ l s m S X q V d cV
  letI a0 : Algebra O Γ(X, V) := (strV q V).toAlgebra
  intro cO cA eO eA hD hD' e hiO hiA he c t hc ha hb
  haveI hF : Module.Flat O Γ(X, V) := GlobalTheory.CompanionTheory.ChartAlg.flat_of_etale cV.t cV.etale
  have hQ : ∀ T, TO q l s {V} T → InU V T := by
    rintro T ⟨-, V', rfl, h⟩
    exact h
  have hQ' : ∀ T, TS γ q l s {V} T → InU V T := by
    rintro T ⟨-, V', rfl, h⟩
    exact h
  have pO := (GlobalTheory.T.chart_divided_powers_graded_constant cO (GlobalTheory.T.chart_is_good cO) (TO q l s {V}) hQ hD).1
  have pA := (GlobalTheory.T.chart_divided_powers_graded_constant cA (GlobalTheory.T.chart_is_good cA) (TS γ q l s {V}) hQ' hD').1
  have bot1 : ∀ r : ℕ, r ≠ 0 → cO.D.pdPow r = ⊥ := fun r hr => by
    rw [pO, dividedPowerFiltration_dividedPowersBot' O hr, Ideal.map_bot]
  have mA : ∀ (r : ℕ) (z : A ⊗[O] Γ(X, V)), eA z ∈ cA.D.pdPow r ↔
      z ∈ (pdP γ r).map (Algebra.TensorProduct.includeLeftRingHom (R := O) (A := A) (B := Γ(X, V))) := fun r z => by
    have h1 : cA.D.i = (eA : A ⊗[O] Γ(X, V) →+* cA.D.B).comp
        (Algebra.TensorProduct.includeLeftRingHom (R := O) (A := A) (B := Γ(X, V))) :=
      RingHom.ext fun a => (hiA a).symm
    rw [pA, h1, ← Ideal.map_map]
    constructor
    · intro h
      obtain ⟨w, hw, h2⟩ := (Ideal.mem_map_iff_of_surjective _ eA.surjective).1 h
      have h3 := eA.injective h2
      rwa [← h3]
    · exact fun h => Ideal.mem_map_of_mem _ h
  have fa : ∀ (i : Fin m) (hu : (t - c).toNat ≤ (i : ℕ)) (hv : (i : ℕ) < t.toNat),
      ∃ θ : Γ(X, V) ≃ₗ[O] sqM (sFil (TO q l s {V}) (t - c - i)) (sFil (TO q l s {V}) (t - i)) ⟨cO.D, hD⟩,
        ∀ x, (θ x).1 = Ideal.Quotient.mk _ (eO (1 ⊗ₜ x)) := fun i hu hv =>
    theta_ex (sFil (TO q l s {V}) (t - c - i)) (sFil (TO q l s {V}) (t - i)) ⟨cO.D, hD⟩
      (by
        change cO.D.pdPow _ = ⊤
        rw [show (t - c - i).toNat = 0 by omega]
        exact cO.D.pdPow_zero)
      (by
        change cO.D.pdPow _ = ⊥
        exact bot1 _ (by omega)) eO hiO
  choose θ hθ using fa
  obtain ⟨π, hs, hk, hπ⟩ := pi_ex (sFil (TS γ q l s {V}) (t - c)) (sFil (TS γ q l s {V}) t) ⟨cA.D, hD'⟩ eA (mA _) (mA _)
  refine GlobalTheory.T.graded_split_range_iso_of_interval (O := O) (A := A) (G := Γ(X, V)) γ m S (t - c).toNat t.toNat θ ?_ π hs hk _ ?_ ?_
  · intro i hi
    by_cases hu : (t - c).toNat ≤ (i : ℕ)
    · refine sub_of_top _ _ _ ?_
      change cO.D.pdPow _ = ⊤
      rw [show (t - i).toNat = 0 by
        have : ¬ (i : ℕ) < t.toNat := fun h => hi ⟨hu, h⟩
        omega]
      exact cO.D.pdPow_zero
    · refine sub_of_bot _ _ _ ?_
      change cO.D.pdPow _ = ⊥
      exact bot1 _ (by omega)
  · intro i n
    simp only [map_zero]
  · intro i n x hu hv hx
    refine Subtype.ext ?_
    rw [hπ]
    have hz := hθ i hu hv x
    generalize θ i hu hv x = z at hz ⊢
    obtain ⟨z, hz'⟩ := z
    change z = _ at hz
    subst hz
    have key : ∀ w : cA.D.B, w = eA (1 ⊗ₜ x) → cA.D.i (S.ν i n) * w = eA (S.ν i n ⊗ₜ x) := by
      rintro _ rfl
      rw [← hiA, ← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    exact congrArg (Ideal.Quotient.mk _) (key _ (he x))

theorem bc_single : KH.LocBc → KH.PolyTf → BcOn True := by
  intro hLoc hPoly O A _ _ _ I γ l s m hO hA S X q 𝒱 h r r' hrr hrs ha hb j
  obtain ⟨-, V, d, rfl, ⟨cV⟩⟩ | ⟨hF, -⟩ := h
  swap
  · exact absurd trivial hF
  obtain ⟨c, hc, rfl⟩ : ∃ c : ℤ, 0 ≤ c ∧ r = r' - c := ⟨r' - r, by omega, by ring⟩
  obtain ⟨cO, eO, tfO, hiO, htO, hevO⟩ := GlobalTheory.T.exists_chart_from_coordinates (O := O) (R := O) (dividedPowersBot O) l s hO q
    (Ideal.Quotient.mk ⊥) (fun _ => rfl) cV
  obtain ⟨cA, eA, tfA, hiA, htA, hevA⟩ := GlobalTheory.T.exists_chart_from_coordinates (O := O) (R := A) γ l s hA q (κA O I) (fun _ => rfl) cV
  obtain ⟨e₀, he₀⟩ := GlobalTheory.T.chart_tensor_base_compat γ q cV cO cA eO eA hiO hiA hevO hevA
  have hQ : ∀ T, TO q l s {V} T → InU V T := by
    rintro T ⟨-, V', rfl, h⟩
    exact h
  have hQ' : ∀ T, TS γ q l s {V} T → InU V T := by
    rintro T ⟨-, V', rfl, h⟩
    exact h
  have hD : TO q l s {V} cO.D := ⟨tfO, V, rfl, cO.inV⟩
  have hD' : TS γ q l s {V} cA.D := ⟨tfA, V, rfl, cA.inV⟩
  have gO := GlobalTheory.T.chart_is_good cO
  have gA := GlobalTheory.T.chart_is_good cA
  let E := cO.frame gO (TO q l s {V}) hQ hD
  let E' := cA.frame gA (TS γ q l s {V}) hQ' hD'
  let e : E.D ⟶ (smO γ q l s {V}).G.obj E'.D := ObjectProperty.homMk e₀
  have he : (smO γ q l s {V}).Fr E E' e := by
    intro i T σ σ'
    have h1 : e₀.φ (cO.t i) = cA.t i := by
      rw [← htO, ← htA]; exact he₀ _
    change (σ'.hom.φ (e₀.φ (cO.t i)) - σ.hom.φ (e₀.φ (cO.t i)) : T.obj.B) = σ'.hom.φ (cA.t i) - σ.hom.φ (cA.t i)
    rw [h1]
  have fil := GlobalTheory.T.sheaf_filtration_property (TO q l s {V})
  have fil' := GlobalTheory.T.sheaf_filtration_property (TS γ q l s {V})
  obtain ⟨PO, hPO⟩ := hPoly (dividedPowersBot O) q (Ideal.Quotient.mk ⊥) l s {V}
  obtain ⟨PA, hPA⟩ := hPoly γ q (κA O I) l s {V}
  have lem : ∀ (i : ℕ) (a : A), a ∈ pdP γ i → ∀ t : ℤ, (smO γ q l s {V}).LeC a (sFil _ (t - i)) (sFil _ t) :=
    fun i a h t => GlobalTheory.T.scalar_multiplication_shifts_filtration γ q l s {V} i a h t
  refine hLoc (smO γ q l s {V}) PO PA E E' e he (fun _ => Function.injective_id) S.N S.ν
    (fun i t => sFil _ (t - c - i)) (fun i t => sFil _ (t - i)) (fun t => sFil _ (t - c)) (fun t => sFil _ t) r'
    (fun i => ⟨fun t T => fil.anti (by omega) T, fun t ht => crit_of PO (hPO (t - c - i) (by omega)).1 rfl
        (fun k => by congr 1; ring),
      fun t ht => crit_of PO (hPO (t - i) (by omega)).1 rfl (fun k => by congr 1; ring)⟩)
    ⟨fun t T => fil'.anti (by omega) T, fun t ht => crit_of PA (hPA (t - c) (by omega)).1 rfl (fun k => by congr 1; ring),
      fun t ht => (hPA t (by omega)).1⟩
    (fun i n t => lem i _ (S.mem i n) _) (fun i n t => lem i _ (S.mem i n) _) ?_ j
  intro t _ _
  exact chart_tens γ l s m S q cV cO cA eO eA hD hD' e hiO hiA he₀ c t hc _ _

end GlobalTheory.CompanionTheory.BcLoc
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PhiBaseLe
section
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B

namespace GlobalTheory.CompanionTheory.CrisFrob

variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l)

def redLe (k : Bool) {m n : ℕ} (h : n ≤ m) : Mor (Lc F κ k m) (Lc F κ k n) ((base l).red h) :=
  B.crMor (F := F) (F' := F) (b := bs l k m) (b' := bs l k n) (ht := rfl) (ht' := rfl) ((base l).red h) rfl
    (dd_red k _ h) (basePt F _ (red_κb κ k h)) fun _ _ _ => rfl

theorem phi_base_le {m n : ℕ} (h : n ≤ m) (B₀ : CommRingCat.{0}) (y : (F.ptK (κb κ true n)).obj B₀) :
    ((phiPt F κ m).app B₀ ((basePt F _ (red_κb κ true h)).app B₀ y)).1.2 =
      ((basePt F _ (red_κb κ true h)).app B₀ ((phiPt F κ n).app B₀ y)).1.2 := by
  rw [SH.phi_snd F κ m B₀ _ (l_zero y.1.1), SH.base_snd, SH.base_snd, SH.phi_snd F κ n B₀ _ (l_zero y.1.1)]

theorem red_phi_le : ∀ {l : ℕ} [Fact l.Prime], ∀ {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l) {m n : ℕ} (h : n ≤ m) (j : ℕ)
    (x : Hc F κ true m j), redHc F κ true h j (phiHc F κ m j x) = phiHc F κ n j (redHc F κ true h j x) := by
  intro l _ O _ F κ m n h j x
  unfold redHc phiHc redMor phiMorC
  exact cr_square (SH.phiM F κ m) (redLe F κ true h) (redLe F κ true h) (SH.phiM F κ n) ((base l).phi_cris m)
    (red_cris _ h) (red_cris _ h) ((base l).phi_cris n) ((pdOk_frob _).red_acr h) (phi_base_le F κ h) j x

end GlobalTheory.CompanionTheory.CrisFrob
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PlanePropOfAllStrongApprox
section
noncomputable section

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published GlobalTheory.CompanionTheory.PlaneSA Topology Sa2 Matrix
  GlobalTheory.CompanionTheory.StrongApproxSub
open Formalism.UG (UJ bc)
open scoped TensorProduct Quaternion

namespace GlobalTheory.CompanionTheory.PlaneSA.OfTwo

section Adelic

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin M) (Fin M) E} {K : Matrix (Fin 2) (Fin 2) E} {a : E}
  {V : Matrix (Fin M) (Fin 2) E} {P : Matrix (Fin 2) (Fin M) E}

theorem sig_incl (e : E) :
    inclR (F := F) (E := E) (AF F) ((σ : E →+* E) e) = sigR (AF F) σ (inclR (F := F) (E := E) (AF F) e) := by
  simp [sigR, inclR]

theorem frameA (h : IsFrame (σ : E →+* E) J K a V P) :
    IsFrame (sigR (AF F) σ) (JR (AF F) J) (JR (AF F) K) (inclR (F := F) (E := E) (AF F) a) (V.map (inclR (F := F) (E := E) (AF F)))
      (P.map (inclR (F := F) (E := E) (AF F))) :=
  h.map (inclR (F := F) (E := E) (AF F)) sig_incl

def iota (h : IsFrame (σ : E →+* E) J K a V P) : HA (AF F) σ K →* HA (AF F) σ J :=
  uHom (frameA h)

theorem mt_iota (h : IsFrame (σ : E →+* E) J K a V P) (g : HA (AF F) σ K) :
    mt (iota h g) = emb0 (V.map (inclR (F := F) (E := E) (AF F))) (P.map (inclR (F := F) (E := E) (AF F))) (mt g) := rfl

theorem continuous_iota (h : IsFrame (σ : E →+* E) J K a V P) :
    Continuous (iota (F := F) h) := by
  haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _
  have hm : Continuous (embHom (frameA (F := F) h).pv) :=
    continuous_const.add (((continuous_const.matrix_mul
      (continuous_id.sub continuous_const))).matrix_mul continuous_const)
  have hu := Continuous.units_map _ hm
  exact Continuous.subtype_mk (hu.comp continuous_subtype_val) _

theorem iota_adelic (h : IsFrame (σ : E →+* E) J K a V P) {g : HA (AF F) σ K}
    (hg : g ∈ SUAdelic σ K) : iota h g ∈ SUAdelic σ J := by
  refine StrongApprox.mem_SUAdelic.2 ?_
  have := StrongApprox.mem_SUAdelic.1 hg
  change (mt (iota h g)).det = 1
  rw [mt_iota, det_frame_embedding (frameA h).pv]
  exact this

theorem iota_rat (h : IsFrame (σ : E →+* E) J K a V P) {γ : HA (AF F) σ K}
    (hγ : γ ∈ SURat σ K) : iota h γ ∈ SURat σ J := by
  refine ⟨iota_adelic h hγ.1, ?_⟩
  obtain ⟨u, hu, e⟩ : (γ : HR (AF F) σ K).1 ∈ (UJ (σ : E →+* E) K).map (bc (inclR (F := F) (E := E) (AF F))) := hγ.2
  change (iota h γ : HR (AF F) σ J).1 ∈ (UJ (σ : E →+* E) J).map (bc (inclR (F := F) (E := E) (AF F)))
  refine ⟨(uHom h ⟨u, hu⟩).1, (uHom h ⟨u, hu⟩).2, Units.ext ?_⟩
  have e' : ((γ : HR (AF F) σ K).1 : Matrix (Fin 2) (Fin 2) (AF F ⊗[F] E)) =
      (u : Matrix (Fin 2) (Fin 2) E).map (inclR (F := F) (E := E) (AF F)) := by
    rw [← e]; rfl
  change (emb0 V P (u : Matrix (Fin 2) (Fin 2) E)).map (inclR (F := F) (E := E) (AF F)) =
    emb0 (V.map (inclR (F := F) (E := E) (AF F))) (P.map (inclR (F := F) (E := E) (AF F)))
      ((γ : HR (AF F) σ K).1 : Matrix (Fin 2) (Fin 2) (AF F ⊗[F] E))
  rw [e']
  exact frame_embedding_map _ _ _ _

theorem iota_supp (h : IsFrame (σ : E →+* E) J K a V P) {u₀ u₁ : Fin M → E}
    (hP : ∀ x : Fin M → E, (hf σ J u₀ x = 0 ∧ hf σ J u₁ x = 0) ↔ P.mulVec x = 0) {ε : AF F}
    {g : HA (AF F) σ K} (hg : g ∈ SUSupp σ K ε) : iota h g ∈ PlaneSupp σ J ε u₀ u₁ := by
  obtain ⟨g1, g2⟩ := mem_SUSupp.1 hg
  refine ⟨mem_SUSupp.2 ⟨iota_adelic h g1, ?_⟩, fun x h0 h1 => ?_⟩
  · have e : mt (iota h g) - 1 =
        V.map (inclR (F := F) (E := E) (AF F)) * (mt g - 1) * P.map (inclR (F := F) (E := E) (AF F)) := by
      rw [mt_iota, emb0, add_sub_cancel_left]
    rw [e, ← Matrix.smul_mul, ← Matrix.mul_smul, g2]
  · have hx : P.mulVec x = 0 := (hP x).1 ⟨h0, h1⟩
    have hv : (P.map (inclR (F := F) (E := E) (AF F))).mulVec (vA x) = 0 := by
      funext k
      have := RingHom.map_mulVec (inclR (F := F) (E := E) (AF F)) P x k
      rw [hx] at this
      have e : vA (F := F) x = (inclR (F := F) (E := E) (AF F)) ∘ x := rfl
      rw [e]
      simpa using this.symm
    change (mt (iota h g)).mulVec (vA x) = vA x
    rw [mt_iota, emb0, Matrix.add_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec, hv,
      Matrix.mulVec_zero, add_zero]

theorem iota_surj (h : IsFrame (σ : E →+* E) J K a V P) (ha : a ≠ 0) (hJ : J.det ≠ 0) {u₀ u₁ : Fin M → E}
    (hP : ∀ x : Fin M → E, (hf σ J u₀ x = 0 ∧ hf σ J u₁ x = 0) ↔ P.mulVec x = 0) {δ : AF F}
    {g : HA (AF F) σ J} (hg : g ∈ PlaneSupp σ J δ u₀ u₁) : ∃ y ∈ SUSupp σ K δ, iota h y = g := by
  obtain ⟨g1, g2⟩ := hg
  obtain ⟨g1a, g1b⟩ := mem_SUSupp.1 g1
  have hq0 : P * (1 - V * P) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, h.pv, Matrix.one_mul, sub_self]
  have hmap : 1 - V.map (inclR (F := F) (E := E) (AF F)) * P.map (inclR (F := F) (E := E) (AF F)) = (1 - V * P).map (inclR (F := F) (E := E) (AF F)) := by
    have h1 : (1 : Matrix (Fin M) (Fin M) E).map (inclR (F := F) (E := E) (AF F)) = 1 :=
      Matrix.map_one _ (map_zero _) (map_one _)
    have h2 : (V * P).map (inclR (F := F) (E := E) (AF F)) = V.map (inclR (F := F) (E := E) (AF F)) * P.map (inclR (F := F) (E := E) (AF F)) :=
      Matrix.map_mul
    rw [← h1, ← h2]
    ext i j
    simp only [Matrix.map_apply, Matrix.sub_apply, map_sub]
  have hq : mt g * (1 - V.map (inclR (F := F) (E := E) (AF F)) * P.map (inclR (F := F) (E := E) (AF F))) =
      1 - V.map (inclR (F := F) (E := E) (AF F)) * P.map (inclR (F := F) (E := E) (AF F)) := by
    rw [hmap]
    ext i j
    have hx : P.mulVec (fun l => (1 - V * P : Matrix (Fin M) (Fin M) E) l j) = 0 := by
      funext k
      exact congrFun (congrFun hq0 k) j
    have := g2 _ ((hP _).2 hx).1 ((hP _).2 hx).2
    exact congrFun this i
  have hab : inclR (F := F) (E := E) (AF F) a⁻¹ * inclR (F := F) (E := E) (AF F) a = 1 := by
    rw [← map_mul, inv_mul_cancel₀ ha, map_one]
  have hL : (J⁻¹).map (inclR (F := F) (E := E) (AF F)) * JR (AF F) J = 1 := by
    have e : (J⁻¹).map (inclR (F := F) (E := E) (AF F)) * J.map (inclR (F := F) (E := E) (AF F)) = (J⁻¹ * J).map (inclR (F := F) (E := E) (AF F)) :=
      Matrix.map_mul.symm
    change (J⁻¹).map (inclR (F := F) (E := E) (AF F)) * J.map (inclR (F := F) (E := E) (AF F)) = 1
    rw [e, Matrix.nonsing_inv_mul _ (IsUnit.mk0 _ hJ)]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  obtain ⟨y, hy1', hy2'⟩ : ∃ y : HA (AF F) σ K, iota h y = g ∧
      mt y = P.map (inclR (F := F) (E := E) (AF F)) * mt g * V.map (inclR (F := F) (E := E) (AF F)) :=
    exists_preimage (frameA (F := F) h) hab hL g hq
  refine ⟨y, mem_SUSupp.2 ⟨StrongApprox.mem_SUAdelic.2 ?_, ?_⟩, hy1'⟩
  · have h1 : (mt g).det = 1 := StrongApprox.mem_SUAdelic.1 g1a
    rw [← hy1', mt_iota, det_frame_embedding (frameA h).pv] at h1
    exact h1
  · have e : mt y - 1 =
        P.map (inclR (F := F) (E := E) (AF F)) * (mt g - 1) * V.map (inclR (F := F) (E := E) (AF F)) := by
      rw [hy2', Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, (frameA (F := F) h).pv]
    rw [e, ← Matrix.smul_mul, ← Matrix.mul_smul, g1b]

end Adelic

theorem plane_prop_of_strong_approx : (∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ β : F, β ≠ 0 → HermitianPlaneStrongApprox σ β) → Sa2.PropPlane := by
  intro hSA F E _ _ _ _ _ σ hcm M J _ hJ S₁ S₂ ε hε u₀ u₁ hnd hnc T₁ T₂ δ hδ
  obtain ⟨β, a, V, P, hβ, ha, h, hP⟩ := exists_frame hcm hJ hnd
  have img : ∀ η : AF F, PlaneSupp σ J η u₀ u₁ = iota h '' SUSupp σ (J2 E β) η := by
    intro η
    ext g
    constructor
    · intro hg
      obtain ⟨y, hy, e⟩ := iota_surj h ha hJ.2 hP hg
      exact ⟨y, hy, e⟩
    · rintro ⟨y, hy, rfl⟩
      exact iota_supp h hP hy
  have hnc2 : ¬ IsCompact (SUSupp σ (J2 E β) ε) := fun hc =>
    hnc (by rw [img ε]; exact hc.image (continuous_iota h))
  have hcl := hSA F E σ hcm β hβ S₁ S₂ ε hε hnc2 T₁ T₂ δ hδ
  rw [img δ]
  rintro _ ⟨g, hg, rfl⟩
  refine closure_mono ?_ (image_closure_subset_closure_image (continuous_iota h) ⟨g, hcl hg, rfl⟩)
  rintro _ ⟨_, ⟨γ, hγ, k, hk, rfl⟩, rfl⟩
  exact ⟨iota h γ, iota_rat h hγ, iota h k, (iota_supp h hP hk).1, map_mul _ _ _⟩

end GlobalTheory.CompanionTheory.PlaneSA.OfTwo

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PushforwardSystemAffineSectionsStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pushforward_system_affine_sections : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X Z : Scheme.{0}} [X.Over (Spec (.of A))] [Z.Over (Spec (.of A))] [IsLocallyNoetherian X] (φ : Z ⟶ X), φ ≫ (X ↘ Spec (.of A)) = (Z ↘ Spec (.of A)) → ∀ {E : X.Modules}, IsCoherent E → ∀ {S : ℕ → Subobject E}, ClosedSys I E S → ∀ (B : Subobject ((Scheme.Modules.pullback φ).obj E)), (∀ e, B ⊔ powSub I _ (e + 1) = pullSys I φ E S e) → ∀ (V : X.Opens), IsAffineOpen V → ∀ x ∈ secs (adjKer φ B) V, ∀ n, ChartIn φ V (secsSub (S n) V) x := by
  first | exact @GlobalTheory.CompanionTheory.GE.Chart.chartIn_adjKer | exact GlobalTheory.CompanionTheory.GE.Chart.chartIn_adjKer | (intros; apply GlobalTheory.CompanionTheory.GE.Chart.chartIn_adjKer <;> assumption)
end

