import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import GroundTheory.Brauer.BaseChangeCSA
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0970
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0963
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0003
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsEqnIffGeneratesAtInv
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0923
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0974
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0913
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0915
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0925
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0916
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0927
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0930
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0951
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0964
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.LowKMultOneP
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.DiscreteSeriesInfinitesimalCharacter
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HolomorphicDiscreteSeries
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle0021
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0965
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0024
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0025

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEigenvectorOfMinpolyRootHermitianPsi
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory.LKMid

theorem roots_eig : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P : Pair G) (v : InfinitePlace G.F) (w : ℂ),
    P.pol.eval₂ v.embedding w = 0 → ∃ x : Fin G.n → ℂ, x ≠ 0 ∧ G.psi v P.γ *ᵥ x = w • x := by
  intro p _ G P v w hw
  letI : Algebra G.F ℂ := v.embedding.toAlgebra
  have hτ : algebraMap G.F ℂ = v.embedding := rfl
  let ψF : G.C →ₐ[G.F] Matrix (Fin G.n) (Fin G.n) ℂ :=
    { G.psi v with
      commutes' := fun x => by
        show G.psi v (algebraMap G.F G.C x) = _
        rw [G.psi_F, Matrix.algebraMap_eq_diagonal]
        rfl }
  let Ψ : ℂ ⊗[G.F] G.C →ₐ[ℂ] Matrix (Fin G.n) (Fin G.n) ℂ :=
    Algebra.TensorProduct.lift (Algebra.ofId ℂ _) ψF (fun a _ => Algebra.commute_algebraMap_left a _)
  haveI : Nontrivial (Matrix (Fin G.n) (Fin G.n) ℂ) := by
    haveI : Nonempty (Fin G.n) := ⟨⟨0, G.n_pos⟩⟩
    infer_instance
  have hinj : Function.Injective Ψ := RingHom.injective (Ψ : ℂ ⊗[G.F] G.C →+* Matrix (Fin G.n) (Fin G.n) ℂ)
  set Γ := G.psi v P.γ with hΓ
  have hΨ : ∀ k : ℕ, Ψ (1 ⊗ₜ ((P.γ : G.C) ^ k)) = Γ ^ k := by
    intro k
    calc Ψ (1 ⊗ₜ ((P.γ : G.C) ^ k)) = Algebra.ofId ℂ (Matrix (Fin G.n) (Fin G.n) ℂ) 1 * ψF ((P.γ : G.C) ^ k) :=
          Algebra.TensorProduct.lift_tmul _ _ _ _ _
      _ = Γ ^ k := by rw [map_one, one_mul, map_pow]; rfl
  have hli0 := Module.Flat.linearIndependent_one_tmul (S := ℂ) (linearIndependent_pow (K := G.F) (P.γ : G.C))
  have hli := hli0.map' Ψ.toLinearMap (LinearMap.ker_eq_bot.2 hinj)
  have hli' : LinearIndependent ℂ (fun i : Fin (minpoly G.F (P.γ : G.C)).natDegree => Γ ^ (i : ℕ)) := by
    have e : (⇑Ψ.toLinearMap ∘ fun i : Fin (minpoly G.F (P.γ : G.C)).natDegree => (1 : ℂ) ⊗ₜ[G.F] ((P.γ : G.C) ^ (i : ℕ))) =
        fun i : Fin (minpoly G.F (P.γ : G.C)).natDegree => Γ ^ (i : ℕ) := by
      funext i
      exact hΨ i
    rw [e] at hli
    exact hli
  have hd : (minpoly G.F (P.γ : G.C)).natDegree = G.n := P.reg.1
  have hint : IsIntegral G.F (P.γ : G.C) := Algebra.IsIntegral.isIntegral _
  have hpm : P.pol.Monic := minpoly.monic hint
  set Q := P.pol.map (algebraMap G.F ℂ) with hQ
  have hQm : Q.Monic := hpm.map _
  have hQdeg : Q.natDegree = G.n := by rw [hQ, hpm.natDegree_map]; exact P.reg.1
  have hQΓ : Polynomial.aeval Γ Q = 0 := by
    rw [hQ, Polynomial.aeval_map_algebraMap]
    have h : Polynomial.aeval (ψF (P.γ : G.C)) P.pol = 0 := by
      rw [Polynomial.aeval_algHom_apply]
      simp [Pair.pol, minpoly.aeval]
    exact h
  have hroot : Q.IsRoot w := by
    rw [Polynomial.IsRoot, hQ, Polynomial.eval_map]; exact hw
  by_contra hne
  push_neg at hne
  have hdet : (Γ - algebraMap ℂ (Matrix (Fin G.n) (Fin G.n) ℂ) w).det ≠ 0 := by
    intro h0
    obtain ⟨x, hx0, hx⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    apply hne x hx0
    rw [Matrix.sub_mulVec, sub_eq_zero] at hx
    rw [hx, Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec, Matrix.one_mulVec]
  set R := Q /ₘ (Polynomial.X - Polynomial.C w) with hRdef
  have hQR : (Polynomial.X - Polynomial.C w) * R = Q := Polynomial.mul_divByMonic_eq_iff_isRoot.2 hroot
  have hRΓ : Polynomial.aeval Γ R = 0 := by
    have h1 := hQΓ
    rw [← hQR, map_mul] at h1
    have hu : IsUnit (Polynomial.aeval Γ (Polynomial.X - Polynomial.C w)) := by
      rw [map_sub, Polynomial.aeval_X, Polynomial.aeval_C, Matrix.isUnit_iff_isUnit_det]
      exact isUnit_iff_ne_zero.2 hdet
    exact (hu.mul_right_eq_zero).1 h1
  have hRd : R.natDegree = G.n - 1 := by
    rw [hRdef, Polynomial.natDegree_divByMonic _ (Polynomial.monic_X_sub_C w), hQdeg, Polynomial.natDegree_X_sub_C]
  have hR0 : R ≠ 0 := by
    intro h
    rw [h, mul_zero] at hQR
    exact hQm.ne_zero hQR.symm
  have hsum : ∑ i : Fin (minpoly G.F (P.γ : G.C)).natDegree, R.coeff i • Γ ^ (i : ℕ) = 0 := by
    rw [Fin.sum_univ_eq_sum_range (fun i => R.coeff i • Γ ^ i), hd, ← hRΓ, Polynomial.aeval_eq_sum_range, hRd,
      Nat.sub_add_cancel G.n_pos]
  have hc := Fintype.linearIndependent_iff.1 hli' (fun i => R.coeff i) hsum ⟨G.n - 1, by rw [hd]; have := G.n_pos; omega⟩
  exact hR0 (Polynomial.leadingCoeff_eq_zero.1 (by rw [Polynomial.leadingCoeff, hRd]; exact hc))

end GlobalTheory.LKMid
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFrobeniusAutomorphismGcd
section
noncomputable section

open ReciprocityTheory.DiscreteGroups.LocalClassField GlobalTheory.LKRes GlobalTheory.LKRes.ResSplit

namespace GlobalTheory.LKRes.ResSplit.Tau

theorem pow_eq_pow_of_modEq' {M : Type*} [Monoid M] {ζ : M} {N a b : ℕ} (hζ : ζ ^ N = 1)
    (h : a ≡ b [MOD N]) : ζ ^ a = ζ ^ b := by
  have h' : a % N = b % N := h
  rw [← Nat.mod_add_div a N, ← Nat.mod_add_div b N, pow_add, pow_add, pow_mul, pow_mul, hζ, one_pow,
    one_pow, h']

theorem pow_modEq_pow_mod (p r a : ℕ) (hp : 1 ≤ p) : p ^ a ≡ p ^ (a % r) [MOD p ^ r - 1] := by
  have h1 : p ^ r ≡ 1 [MOD p ^ r - 1] := ((Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ hp)).2 dvd_rfl).symm
  have h2 := (Nat.ModEq.pow (a / r) h1).mul_left (p ^ (a % r))
  rw [one_pow, mul_one, ← pow_mul, ← pow_add, Nat.mod_add_div] at h2
  exact h2

variable {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)}

theorem pow_fix {σ : PadicAlgCl p ≃ₐ[K] PadicAlgCl p} {x : PadicAlgCl p} (h : σ x = x) (n : ℕ) :
    (σ ^ n) x = x := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ', AlgEquiv.mul_apply, ih, h]

theorem pow_apply_root' {σ : PadicAlgCl p ≃ₐ[K] PadicAlgCl p} {q N : ℕ}
    (h : ∀ ζ : PadicAlgCl p, ζ ^ N = 1 → σ ζ = ζ ^ q) {ζ : PadicAlgCl p} (hζ : ζ ^ N = 1) (k : ℕ) :
    (σ ^ k) ζ = ζ ^ q ^ k := by
  induction k with
  | zero => simp
  | succ n ih =>
    have h1 : (ζ ^ q ^ n) ^ N = 1 := by rw [← pow_mul, mul_comm, pow_mul, hζ, one_pow]
    rw [pow_succ', AlgEquiv.mul_apply, ih, h _ h1, ← pow_mul, pow_succ]

theorem frob_pow_mod (hK : FiniteDimensional ℚ_[p] K) {m : ℕ} (hm : 0 < m) {x : PadicAlgCl p}
    (hx : x ∈ Kn p K m) (a : ℕ) : (frobK p K ^ a) x = (frobK p K ^ (a % m)) x := by
  have h := (IsFrobOn.pow_fixes_iff p K hK hm ((isFrob_frobK hK).isFrobOn m) (m * (a / m))).2
    (dvd_mul_right _ _)
  conv_lhs => rw [← Nat.mod_add_div a m, pow_add, AlgEquiv.mul_apply, h x hx]

theorem exists_tau : ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)),
    FiniteDimensional ℚ_[p] K → ∀ (f r : ℕ) (hq : qK p K = p ^ f), 0 < r →
    ∃ τ : Kn p K (r / Nat.gcd f r) ≃+* Kn p K (r / Nat.gcd f r),
      (∀ x, τ x = x ↔ (x : PadicAlgCl p) ∈ K) ∧ (∀ x, (⇑τ)^[r / Nat.gcd f r] x = x) ∧
      ∀ b : Qr p r, τ (incQ p K hq r b) = incQ p K hq r ((frobQ p r ^ Nat.gcd f r) b) := by
  intro p _ K hK f r hq hr
  have hp0 : 0 < p := (Nat.Prime.one_lt Fact.out).le
  have hd0 : 0 < Nat.gcd f r := Nat.gcd_pos_of_pos_right f hr
  have hm0 : 0 < r / Nat.gcd f r := Nat.div_pos (Nat.gcd_le_right (m := f) (n := r) hr) hd0
  have hrdm : r = Nat.gcd f r * (r / Nat.gcd f r) := (Nat.mul_div_cancel' (Nat.gcd_dvd_right f r)).symm
  have hfdf : f = Nat.gcd f r * (f / Nat.gcd f r) := (Nat.mul_div_cancel' (Nat.gcd_dvd_left f r)).symm
  have hcop : Nat.Coprime (f / Nat.gcd f r) (r / Nat.gcd f r) := Nat.coprime_div_gcd_div_gcd hd0
  set d := Nat.gcd f r with hd
  set m := r / d with hm
  set f' := f / d with hf'
  set k := f' ^ (Nat.totient m - 1) with hk
  have hk1 : f' * k ≡ 1 [MOD m] := by
    have ht : 0 < Nat.totient m := Nat.totient_pos.2 hm0
    have := Nat.ModEq.pow_totient hcop
    rwa [← Nat.sub_add_cancel ht, pow_succ'] at this
  have hk2 : f * k ≡ d [MOD r] := by
    have := Nat.ModEq.mul_left' d hk1
    rw [mul_one, ← mul_assoc, ← hfdf, ← hrdm] at this
    exact this
  let σ : PadicAlgCl p ≃ₐ[K] PadicAlgCl p := frobK p K ^ k
  have hσ : ∀ x ∈ Kn p K m, σ x ∈ Kn p K m := fun x hx => UnramifiedExtensions.map_mem_Kn K m σ hx
  have hσ' : ∀ x ∈ Kn p K m, σ⁻¹ x ∈ Kn p K m := fun x hx => UnramifiedExtensions.map_mem_Kn K m σ⁻¹ hx
  let τ : Kn p K m ≃+* Kn p K m :=
    { toFun := fun x => ⟨σ x, hσ x x.2⟩
      invFun := fun x => ⟨σ⁻¹ x, hσ' x x.2⟩
      left_inv := fun x => Subtype.ext (by
        show σ⁻¹ (σ (x : PadicAlgCl p)) = x
        rw [AlgEquiv.aut_inv, AlgEquiv.symm_apply_apply])
      right_inv := fun x => Subtype.ext (by
        show σ (σ⁻¹ (x : PadicAlgCl p)) = x
        rw [AlgEquiv.aut_inv, AlgEquiv.apply_symm_apply])
      map_mul' := fun x y => Subtype.ext (map_mul σ (x : PadicAlgCl p) y)
      map_add' := fun x y => Subtype.ext (map_add σ (x : PadicAlgCl p) y) }
  have hτ : ∀ x, ((τ x : Kn p K m) : PadicAlgCl p) = σ x := fun _ => rfl
  refine ⟨τ, fun x => ⟨fun h => ?_, fun h => ?_⟩, fun x => ?_, fun b => ?_⟩
  · have h1 : σ x = x := by rw [← hτ, h]
    have h2 : (frobK p K ^ (k * f')) x = x := by rw [pow_mul]; exact pow_fix h1 f'
    have h3 : frobK p K (x : PadicAlgCl p) = x := by
      have e := frob_pow_mod hK hm0 x.2 (k * f')
      have e1 := frob_pow_mod hK hm0 x.2 1
      rw [pow_one] at e1
      have e2 : (k * f') % m = 1 % m := by rw [mul_comm]; exact hk1
      rw [e1, ← e2, ← e, h2]
    exact mem_of_frobK_fixed hK (Kn_le_Kur hm0 x.2) h3
  · exact Subtype.ext (show σ (x : PadicAlgCl p) = x from σ.commutes ⟨x, h⟩)
  · have hit : ∀ n (y : Kn p K m), (((⇑τ)^[n] y : Kn p K m) : PadicAlgCl p) = (σ ^ n) y := by
      intro n
      induction n with
      | zero => intro y; rfl
      | succ n ih =>
        intro y
        rw [Function.iterate_succ_apply', pow_succ', AlgEquiv.mul_apply, ← ih]
        rfl
    apply Subtype.ext
    rw [hit, ← pow_mul, frob_pow_mod hK hm0 x.2, show k * m % m = 0 by simp, pow_zero]
    rfl
  · have hN : ¬ p ∣ p ^ r - 1 := by
      intro h
      have h2 := Nat.dvd_sub (dvd_pow_self p hr.ne') h
      rw [Nat.sub_sub_self (Nat.one_le_pow _ _ hp0)] at h2
      exact (Nat.Prime.one_lt Fact.out).ne' (Nat.dvd_one.1 h2)
    have hpow : p ^ (f * k) ≡ p ^ d [MOD p ^ r - 1] := by
      have e := pow_modEq_pow_mod p r (f * k) hp0
      rw [show f * k % r = d % r from hk2] at e
      exact e.trans (pow_modEq_pow_mod p r d hp0).symm
    apply Subtype.ext
    rw [hτ, coe_incQ, coe_incQ, coe_frobQ_pow]
    refine UnramifiedExtensions.eqOn_Kn (Q0 p) (σ := resGK bot_le σ) (τ := frobK p (Q0 p) ^ d) (fun ζ hζ => ?_) b.2
    rw [residue_cardinality_base_field] at hζ
    rw [resGK_apply, frobenius_pow_root_of_unity p hN hζ d]
    have hfr := fun ζ' hζ' => (isFrob_iff hK (frobK p K)).1 (isFrob_frobK hK) ζ' (p ^ r - 1) hN hζ'
    show (frobK p K ^ k) ζ = _
    rw [pow_apply_root' hfr hζ k, hq, ← pow_mul]
    exact pow_eq_pow_of_modEq' hζ hpow

end GlobalTheory.LKRes.ResSplit.Tau
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlobalSectionUnitStalkStatement
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits GlobalTheory.Cartier
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_global_section_unit_stalk : ∀ (Y Z : Scheme.{0}) (ι : Y ⟶ Z) (D : LB Z), D.IsLB → ∀ t : (D.pull ι).Gen, t.IsGen →
  ∀ (M : ℕ) (a : ∀ i, Γ(Z, D.U i)),
  (∀ i j, ReciprocityTheory.ChartRestriction.G.Geo.Tor.resG Z (inf_le_left : D.U i ⊓ D.U j ≤ D.U i) (a i) * ((D.g i j : Γ(Z, D.U i ⊓ D.U j))) ^ M =
    ReciprocityTheory.ChartRestriction.G.Geo.Tor.resG Z (inf_le_right : D.U i ⊓ D.U j ≤ D.U j) (a j)) →
  ∃ h : Γ(Y, ⊤), ∀ (i : D.ι) (y : Y) (hy : ι y ∈ D.U i), ∃ u : (Y.presheaf.stalk y)ˣ,
    (Y.presheaf.germ ⊤ y trivial).hom h = (ι.stalkMap y).hom ((Z.presheaf.germ (D.U i) (ι y) hy).hom (a i)) * (u : Y.presheaf.stalk y) := by
  first | exact @GlobalTheory.DivGlue.glue | exact GlobalTheory.DivGlue.glue | (intros; apply GlobalTheory.DivGlue.glue <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlueRigidifiedLineBundleClasses
section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.PicGlue Opposite
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PicGlue

theorem exists_glue_rigidified (X Y : Scheme.{0}) (p : X ⟶ Y) (e : Y ⟶ X) (hep : e ≫ p = 𝟙 Y) (hp : FnBij p)
    (Ix : Type) (X' : Ix → Scheme.{0}) (f : ∀ i, X' i ⟶ X) (V : Ix → Y.Opens) (c : ∀ i, Pic (X' i))
    (hf : ∀ i, IsOpenImmersion (f i)) (hr : ∀ i x, x ∈ Set.range (f i) ↔ p x ∈ V i) (hV : ∀ y, ∃ i, y ∈ V i)
    (hrig : ∀ (i : Ix) (T : Scheme.{0}) (t : T ⟶ X' i) (s : T ⟶ Y), t ≫ f i = s ≫ e → GlobalTheory.CechPic.pull t (c i) = 0)
    (hov : ∀ (i k : Ix) (T : Scheme.{0}) (a : T ⟶ X' i) (b : T ⟶ X' k), a ≫ f i = b ≫ f k →
      GlobalTheory.CechPic.pull a (c i) = GlobalTheory.CechPic.pull b (c k)) :
    ∃ c₀ : Pic X, GlobalTheory.CechPic.pull e c₀ = 0 ∧ ∀ i, GlobalTheory.CechPic.pull (f i) c₀ = c i := by
  have hpe : ∀ y : Y, p (e y) = y := fun y ↦ by
    rw [← Scheme.Hom.comp_apply, hep]; rfl
  have hrange : ∀ i, (f i).opensRange = p ⁻¹ᵁ V i := fun i ↦ by
    ext x; exact hr i x
  choose M hM hMc using fun i ↦ cls_surj (c i)
  choose L hL hLM using fun i ↦ GlobalTheory.T.exists_cech_lineBundle_ambient_of_openImmersion X (X' i) (f i) (M i) (hM i)
  have hL' : ∀ i, IsOn (p ⁻¹ᵁ V i) (L i) := fun i ↦ hrange i ▸ hL i
  have hfm : ∀ i (z : X' i), f i z ∈ p ⁻¹ᵁ V i := fun i z ↦ (hr i _).1 ⟨z, rfl⟩
  have hfl : ∀ i, ((L i).pull (f i)).IsLB := fun i ↦ GlobalTheory.T.isLineBundle_pull_of_isLineBundleOnOpen X _ _ (L i) (f i) (hL' i) (hfm i)
  have hcl : ∀ i, cls _ (hfl i) = c i := fun i ↦ ((cls_eq_iff (hfl i) (hM i)).2 (hLM i)).trans (hMc i)
  have lifts : ∀ i (T : Scheme.{0}) (g : T ⟶ X), (∀ z, g z ∈ p ⁻¹ᵁ V i) → ∃ t : T ⟶ X' i, t ≫ f i = g :=
    fun i T g hg ↦ ⟨IsOpenImmersion.lift (f i) g (by rintro _ ⟨z, rfl⟩; exact (hr i _).2 (hg z)),
      IsOpenImmersion.lift_fac _ _ _⟩
  have hpl : ∀ i (T : Scheme.{0}) (t : T ⟶ X' i) (g : T ⟶ X), t ≫ f i = g →
      ∃ h : ((L i).pull g).IsLB, cls _ h = GlobalTheory.CechPic.pull t (c i) := by
    rintro i T t _ rfl
    have h : ((L i).pull (t ≫ f i)).IsLB := GlobalTheory.T.isLineBundle_pull_of_isLineBundleOnOpen X _ _ (L i) _ (hL' i) fun z ↦ by
      rw [Scheme.Hom.comp_apply]; exact hfm i _
    refine ⟨h, ?_⟩
    rw [← hcl i, ← cls_pull (hfl i) t (pull_isLB (hfl i) t)]
    exact ((cls_eq_iff _ _).2 (GlobalTheory.T.lineBundleOnOpen_pull_comp_iso X _ _ _ (L i) (f i) t (hL' i) (hfm i))).symm
  have hR : ∀ i, ∃ r : RigD e (L i), RigOn e (L i) r := fun i ↦ by
    refine GlobalTheory.T.exists_pullbackGenerator_of_trivial_on_open X Y e (V i) (L i) (fun a y hy ↦ ?_) ?_
    · have : p (e y) ∈ V i := (hL' i).le a hy
      rwa [hpe] at this
    · obtain ⟨t, ht⟩ := lifts i _ ((V i).ι ≫ e) fun z ↦ by
        rw [Scheme.Hom.comp_apply]
        change p (e _) ∈ V i
        rw [hpe]
        exact z.2
      obtain ⟨h, hc⟩ := hpl i _ t _ ht
      exact (cls_eq_zero_iff h).1 (hc.trans (hrig i _ t _ ht))
  choose r hr' using hR
  have hw : ∀ i k, ∃ w : Cmp (p ⁻¹ᵁ (V i ⊓ V k)) (L i) (L k), IsoOn (p ⁻¹ᵁ (V i ⊓ V k)) (L i) (L k) w ∧
      Norm e (p ⁻¹ᵁ (V i ⊓ V k)) (L i) (L k) w (r i) (r k) := fun i k ↦ by
    obtain ⟨a, ha⟩ := lifts i _ (p ⁻¹ᵁ (V i ⊓ V k)).ι fun z ↦ z.2.1
    obtain ⟨b, hb⟩ := lifts k _ (p ⁻¹ᵁ (V i ⊓ V k)).ι fun z ↦ z.2.2
    obtain ⟨h1, e1⟩ := hpl i _ a _ ha
    obtain ⟨h2, e2⟩ := hpl k _ b _ hb
    obtain ⟨w, hw⟩ := GlobalTheory.T.exists_isLineBundleIsoOnOpen_of_restriction_iso X (p ⁻¹ᵁ (V i ⊓ V k)) (L i) (L k)
      ((cls_eq_iff h1 h2).1 (e1.trans ((hov i k _ a b (ha.trans hb.symm)).trans e2.symm)))
    exact GlobalTheory.T.exists_lineBundleIso_normalisedAlongSection_retraction X Y p e hep (V i ⊓ V k) _ _ (L i) (L k) w (r i) (r k) (hL' i) (hL' k)
      (fun _ h ↦ h.1) (fun _ h ↦ h.2) hw (hr' i) (hr' k)
  choose w hwi hwn using hw
  obtain ⟨N, hN, hv⟩ := GlobalTheory.T.lineBundle_glue_of_openCover_cocycle X Ix (fun i ↦ p ⁻¹ᵁ V i) L w (fun x ↦ hV (p x)) hL' hwi
    fun i j k x a b d ha hb hd ↦ GlobalTheory.T.normalised_lineBundleIso_cocycle_identity X Y p e hep hp (V i ⊓ V j ⊓ V k) _ _ _ _ _ _ (L i) (L j) (L k)
      (w i j) (w j k) (w i k) (r i) (r j) (r k) (hL' i) (hL' j) (hL' k) (fun _ h ↦ h)
      (fun _ h ↦ ⟨⟨h.1, h.1.2, h.2⟩, h.1.1, h.2⟩) (hwi i j) (hwi j k) (hwi i k) (hwn i j) (hwn j k) (hwn i k)
      x a b d ⟨⟨(hL' i).le a ha, (hL' j).le b hb⟩, (hL' k).le d hd⟩ ha hb hd
  have hNc : ∀ i, GlobalTheory.CechPic.pull (f i) (cls N hN) = c i := fun i ↦ by
    obtain ⟨v, hv⟩ := hv i
    rw [← hcl i, ← cls_pull hN (f i) (pull_isLB hN _)]
    exact (cls_eq_iff _ _).2 (GlobalTheory.T.lineBundleIso_pull_of_isLineBundleIsoOnOpen X _ _ N (L i) v (f i) hv (hfm i))
  refine ⟨cls N hN - GlobalTheory.CechPic.pull p (GlobalTheory.CechPic.pull e (cls N hN)), ?_, fun i ↦ ?_⟩
  · rw [map_sub, ← pull_comp e p, hep, pull_id, sub_self]
  · obtain ⟨t, ht⟩ := lifts i _ ((f i ≫ p) ≫ e) fun z ↦ by
      rw [Scheme.Hom.comp_apply]
      change p (e _) ∈ V i
      rw [hpe, Scheme.Hom.comp_apply]
      exact hfm i z
    rw [map_sub, hNc, ← pull_comp (f i) p, ← pull_comp (f i ≫ p) e, ← ht, pull_comp, hNc,
      hrig i _ t _ ht, sub_zero]

end GlobalTheory.PicGlue
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegersApproximatingRootOfUnityTwists
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PrimePart

open NumberField MvPowerSeries IsLocalRing ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FGDepth GlobalTheory.CharDepth
  GlobalTheory.FactorDepth GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes

theorem v_pow_sub_pow_lt_one {C : Type} [Field C] (v : Valuation C NNReal) {x y : C} (hx : v x ≤ 1) (hy : v y ≤ 1)
    (hxy : v (x - y) < 1) (n : ℕ) : v (x ^ n - y ^ n) < 1 := by
  rw [← geom_sum₂_mul x y n, map_mul]
  have hs : v (∑ i ∈ Finset.range n, x ^ i * y ^ (n - 1 - i)) ≤ 1 := by
    apply Valuation.map_sum_le
    intro i _
    rw [map_mul, map_pow, map_pow]
    exact mul_le_one₀ (pow_le_one₀ zero_le hx) zero_le (pow_le_one₀ zero_le hy)
  calc v (∑ i ∈ Finset.range n, x ^ i * y ^ (n - 1 - i)) * v (x - y) ≤ 1 * v (x - y) :=
        mul_le_mul_of_nonneg_right hs zero_le
    _ = v (x - y) := one_mul _
    _ < 1 := hxy

private lemma exists_mem_sub_one_mem_of_maximal_ne {R : Type} [CommRing R] {P Q : Ideal R} (hP : P.IsMaximal)
    (hQ : Q.IsMaximal) (h : P ≠ Q) : ∃ a ∈ P, a - 1 ∈ Q := by
  have htop : P ⊔ Q = ⊤ := Ideal.IsMaximal.coprime_of_ne hP hQ h
  have h1 : (1 : R) ∈ P ⊔ Q := by rw [htop]; exact Submodule.mem_top
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 h1
  refine ⟨a, ha, ?_⟩
  have hb' : a - 1 = -b := by rw [← hab]; ring
  rw [hb']
  exact Q.neg_mem hb

theorem exists_sub_one_mem_and_mem {R ι : Type} [CommRing R] [Finite ι] (P : ι → Ideal R) (hP : ∀ i, (P i).IsMaximal)
    (t : ι) : ∃ e : R, e - 1 ∈ P t ∧ ∀ i, P i ≠ P t → e ∈ P i := by
  classical
  haveI := Fintype.ofFinite ι
  have hc : ∀ i, ∃ a : R, (P i ≠ P t → a ∈ P i) ∧ a - 1 ∈ P t := by
    intro i
    by_cases hi : P i = P t
    · exact ⟨1, fun h => absurd hi h, by simp⟩
    · obtain ⟨a, ha, ha1⟩ := exists_mem_sub_one_mem_of_maximal_ne (hP i) (hP t) hi
      exact ⟨a, fun _ => ha, ha1⟩
  choose a ha using hc
  refine ⟨∏ i, a i, ?_, ?_⟩
  · refine Ideal.Quotient.eq.1 ?_
    rw [map_prod, map_one]
    exact Finset.prod_eq_one fun i _ => by
      rw [← map_one (Ideal.Quotient.mk (P t))]
      exact Ideal.Quotient.eq.2 (ha i).2
  · intro i hi
    rw [← Finset.mul_prod_erase Finset.univ a (Finset.mem_univ i)]
    exact Ideal.mul_mem_right _ _ ((ha i).1 hi)

private lemma pow_pow_mul_eq_self_of_pow_sub_one_eq_one {C : Type} [Field C] {z : C} {h : ℕ} (p : ℕ) (hp : 0 < p)
    (hz : z ^ (p ^ h - 1) = 1) (M : ℕ) : z ^ p ^ (h * M) = z := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Nat.mul_succ, pow_add, pow_mul, ih]
    have hph : p ^ h = p ^ h - 1 + 1 := (Nat.sub_add_cancel (Nat.one_le_pow _ _ hp)).symm
    rw [hph, pow_succ, hz, one_mul]

theorem exists_approx_root_twists : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Level H) (c : Coeff l) (p : ℕ) [Fact p.Prime] (T : CDVR) (io : c.F →+* T.Fr) (X : ValExt T p), ∀ (τ : E →+* ℂ) (h : ℕ), 0 < h → ∀ (lab : ZMod h → (E →+* ℂ)), (∀ s a, X.v (embX io X (lab s) a - embX io X τ a ^ p ^ s.val) < 1) → ∀ z : X.C, z ^ (p ^ h - 1) = 1 → (∃ a₀ : 𝓞 E, X.v (embX io X τ a₀ - z) < 1) → ∀ r : ℝ, ∃ a : 𝓞 E, (∀ s, (r : WithTop ℝ) ≤ vX_vp X (embX io X (lab s) a - z ^ p ^ s.val)) ∧ ∀ σ, primeBelow io X σ ≠ primeBelow io X τ → (r : WithTop ℝ) ≤ vX_vp X (embX io X σ a) := by
  intro E _ _ _ H l c p _ T io X τ h hh lab hlab z hz ha₀ r
  classical
  obtain ⟨a₀, ha₀⟩ := ha₀
  have hp : p.Prime := Fact.out
  haveI : NeZero h := ⟨hh.ne'⟩
  obtain ⟨e, he1, he⟩ := exists_sub_one_mem_and_mem (fun σ : E →+* ℂ => primeBelow io X σ)
    (fun σ => (primeBelow_isMaximal_card E H l c p T io X σ).1) τ
  have hv1 : ∀ σ a, X.v (embX io X σ a) ≤ 1 := fun σ a => v_embX_le_one io X σ a
  have hvz : X.v z ≤ 1 := by
    have hn : p ^ h - 1 ≠ 0 := by
      have : 2 ≤ p ^ h := le_trans hp.two_le (Nat.le_self_pow hh.ne' p)
      omega
    have h1 : X.v z ^ (p ^ h - 1) ≤ 1 := by rw [← map_pow, hz, map_one]
    exact (pow_le_one_iff_of_nonneg zero_le hn).1 h1
  have hvzs : ∀ n : ℕ, X.v (z ^ n) ≤ 1 := fun n => by rw [map_pow]; exact pow_le_one₀ zero_le hvz
  have he1' : X.v (embX io X τ e - 1) < 1 := by
    have : X.v (embX io X τ (e - 1)) < 1 := he1
    rwa [map_sub, map_one] at this
  have hτb : X.v (embX io X τ (e * a₀) - z) < 1 := by
    have hsplit : embX io X τ (e * a₀) - z =
        (embX io X τ e - 1) * embX io X τ a₀ + (embX io X τ a₀ - z) := by rw [map_mul]; ring
    rw [hsplit]
    refine Valuation.map_add_lt _ ?_ ha₀
    rw [map_mul]
    exact mul_lt_one_of_nonneg_of_lt_one_left zero_le he1' (hv1 τ a₀)
  have hlabb : ∀ s : ZMod h, X.v (embX io X (lab s) (e * a₀) - z ^ p ^ s.val) < 1 := by
    intro s
    have hsplit : embX io X (lab s) (e * a₀) - z ^ p ^ s.val =
        (embX io X (lab s) (e * a₀) - embX io X τ (e * a₀) ^ p ^ s.val) +
          (embX io X τ (e * a₀) ^ p ^ s.val - z ^ p ^ s.val) := by ring
    rw [hsplit]
    exact Valuation.map_add_lt _ (hlab s (e * a₀))
      (v_pow_sub_pow_lt_one X.v (hv1 τ _) hvz hτb _)
  have hoth : ∀ σ, primeBelow io X σ ≠ primeBelow io X τ → X.v (embX io X σ (e * a₀)) < 1 := by
    intro σ hσ
    have hmem : X.v (embX io X σ e) < 1 := he σ hσ
    rw [map_mul, map_mul]
    exact mul_lt_one_of_nonneg_of_lt_one_left zero_le hmem (hv1 σ a₀)
  have hs : ∀ s : ZMod h, ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → (r : WithTop ℝ) ≤
      vX_vp X (embX io X (lab s) (e * a₀) ^ p ^ N - (z ^ p ^ s.val) ^ p ^ N) := by
    intro s
    exact GlobalTheory.T.exists_valuation_pow_primePow_sub_ge X.C (vX_vp X) p hp (vX_vp_p X) _ _ ((isIntV_iff X _).2 (hv1 _ _))
      ((isIntV_iff X _).2 (hvzs _)) ((vX_vp_pos_iff X _).2 (hlabb s)) r
  have hσ : ∀ σ : E →+* ℂ, ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → primeBelow io X σ ≠ primeBelow io X τ →
      (r : WithTop ℝ) ≤ vX_vp X (embX io X σ (e * a₀) ^ p ^ N) := by
    intro σ
    by_cases hne : primeBelow io X σ = primeBelow io X τ
    · exact ⟨0, fun _ _ h' => absurd hne h'⟩
    · have hlt : X.v (embX io X σ (e * a₀) - 0) < 1 := by rw [sub_zero]; exact hoth σ hne
      obtain ⟨N₀, hN₀⟩ := GlobalTheory.T.exists_valuation_pow_primePow_sub_ge X.C (vX_vp X) p hp (vX_vp_p X) _ 0 ((isIntV_iff X _).2 (hv1 _ _))
        ((isIntV_iff X _).2 (by simp)) ((vX_vp_pos_iff X _).2 hlt) r
      refine ⟨N₀, fun N hN _ => ?_⟩
      have := hN₀ N hN
      rwa [zero_pow (pow_ne_zero _ hp.ne_zero), sub_zero] at this
  choose Ns hNs using hs
  choose Nσ hNσ using hσ
  set M := (∑ s, Ns s) + ∑ σ, Nσ σ with hM
  have hMN : M ≤ h * M := Nat.le_mul_of_pos_left M hh
  refine ⟨(e * a₀) ^ p ^ (h * M), fun s => ?_, fun σ hne => ?_⟩
  · have hzN : (z ^ p ^ s.val) ^ p ^ (h * M) = z ^ p ^ s.val := by
      rw [← pow_mul, mul_comm, pow_mul, pow_pow_mul_eq_self_of_pow_sub_one_eq_one p hp.pos hz M]
    have hle : Ns s ≤ h * M :=
      le_trans (le_trans (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ s))
        (Nat.le_add_right _ _)) hMN
    have := hNs s (h * M) hle
    rwa [hzN, ← map_pow] at this
  · have hle : Nσ σ ≤ h * M :=
      le_trans (le_trans (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ σ))
        (Nat.le_add_left _ _)) hMN
    have := hNσ σ (h * M) hle hne
    rwa [← map_pow] at this

end GlobalTheory.PrimePart
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKFiniteModuleIrreducibleUnitary
section
open Matrix GlobalTheory.HolDS
open Formalism.REAL (GlRel IsUnitary IsWeight KHighest root Jm inG)
open Formalism.QuantumDeterminants (lowK IsHCParam)
open Formalism.MainNotions.S (IsURepOn IsIrredOn UJset IsKFin IsKTypeOf IsKStableOn IsDS lowKSub vNormSq)
open CompanionTheory.D.DSIC (KRel KUnit KStab IsSmMod)
open CompanionTheory.D.LK (IsKMod IsMin)
open scoped InnerProductSpace

namespace GlobalTheory.CompanionTheory.KModExistsStep

theorem kModExists_holds : CompanionTheory.D.LK.KModExists :=
  GlobalTheory.CompanionTheory.KModExists.kModExists CompanionTheory.D.DSIC.hSmMod CompanionTheory.D.gk.admitted.kFin_mem_smoothVecs CompanionTheory.D.DSIC.hKFinStab
    CompanionTheory.D.DSIC.hStabLink CompanionTheory.D.DSIC.hHWofType CompanionTheory.D.DSIC.hTypeOfHW

end GlobalTheory.CompanionTheory.KModExistsStep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLatticeAutomorphismModHalfLevelStatement
section
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Mult
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lattice_automorphism_mod_halfLevel : ∀ (D : D7) (V : HSp D) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)), LatEmb V ι → ∀ κ ∈ GlobalTheory.IndefiniteRowSideFullHecke.EmbeddingLevelSets.levSet V 1, ∃ γ : GlobalTheory.IndefiniteRowSideFullHecke.LevelLiftConditions.LevGrp Dw l, ∀ a : Dw.La, (finHom V κ).1.mulVec (finVec V (ι a)) - finVec V (ι (liftLa γ a)) ∈ AddSubgroup.closure {u | ∃ b ∈ l.Mb, ∃ z ∈ latGHat V 1, u = halfVec V b z} := by
  first | exact @GlobalTheory.StabInduce.exists_levGrp_induced | exact GlobalTheory.StabInduce.exists_levGrp_induced | (intros; apply GlobalTheory.StabInduce.exists_levGrp_induced <;> assumption)
end

