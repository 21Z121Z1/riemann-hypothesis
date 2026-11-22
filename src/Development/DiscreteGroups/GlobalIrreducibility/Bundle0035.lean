import Mathlib
import Development.DiscreteGroups.GlobalIrreducibility.DzMatchCut
import Development.DiscreteGroups.GlobalIrreducibility.Bundle0029
import Development.DiscreteGroups.GlobalIrreducibility.Bundle0030
import Development.DiscreteGroups.GlobalIrreducibility.ExistsIneOfVEqOne
import Development.DiscreteGroups.GlobalIrreducibility.DzIneEq
import Development.DiscreteGroups.GlobalIrreducibility.Bundle0014
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0646
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0786
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0783
import Development.DiscreteGroups.GlobalIrreducibility.Bundle0018
import Development.DiscreteGroups.GlobalIrreducibility.ExistsCellFunctional
import Development.DiscreteGroups.GlobalIrreducibility.Bundle0031

-- bundled from Development.DiscreteGroups.GlobalIrreducibility.EqTraceSmulOfFinrankOne
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GLq
  GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL Matrix
open scoped Pointwise

namespace DiscreteGroups.sglob.DzType

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem ine_restrict {E E' Ω : Type} [Field E] [NumberField E] [Field E'] [NumberField E'] [Field Ω] [Algebra E E']
    [Algebra E Ω] [Algebra E' Ω] [IsScalarTower E E' Ω] {A : ValuationSubring Ω} (t : Ine (F := E') A) :
    AlgEquiv.restrictScalars E (t : G E' Ω) ∈ Ine (F := E) A := by
  refine ⟨?_, fun x hx => t.2.2 x hx⟩
  show AlgEquiv.restrictScalars E (t : G E' Ω) • A = A
  have hd : (t : G E' Ω) • A = A := t.2.1
  ext y
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
  conv_rhs => rw [← hd]
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
  exact Iff.rfl

theorem eq_trace_smul_of_finrank_one {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (hV : Module.finrank ℂ V = 1) (f : V →ₗ[ℂ] V) (v : V) : f v = (LinearMap.trace ℂ V f) • v := by
  obtain ⟨b, -, hspan⟩ := finrank_eq_one_iff'.1 hV
  obtain ⟨c₀, hc₀⟩ := hspan (f b)
  have hf : f = c₀ • LinearMap.id := by
    ext w
    obtain ⟨c, rfl⟩ := hspan w
    rw [map_smul, ← hc₀, LinearMap.smul_apply, LinearMap.id_apply, smul_comm]
  rw [hf, map_smul, LinearMap.trace_id, hV, Nat.cast_one, smul_eq_mul, mul_one, LinearMap.smul_apply,
    LinearMap.id_apply]

theorem charpoly_fin_one {R : Type} [CommRing R] (M : Matrix (Fin 1) (Fin 1) R) : M.charpoly = X - C (M 0 0) := by
  simp [Matrix.charpoly, Matrix.det_unique]

theorem tau_scalar (g : ℕ) [Fact g.Prime] (K : Type) [Field K] [Algebra (ZMod g) K] (θ : Kˣ →* ℂˣ)
    (τ : FDRep ℂ (Gn g 1))
    (hf : ∀ y : Gn g 1, Irreducible (y : Mt g 1).charpoly → ∀ z : Kˣ, aeval (z : K) (y : Mt g 1).charpoly = 0 →
        τ.character y = (-1) ^ (1 - 1) * ∑ j ∈ Finset.range 1, ((θ (z ^ g ^ j) : ℂˣ) : ℂ))
    (y : Gn g 1) (z : Kˣ) (hz : (z : K) = algebraMap (ZMod g) K ((y : Mt g 1) 0 0)) (v : τ) :
    τ.ρ y v = ((θ z : ℂˣ) : ℂ) • v := by
  have key : ∀ (y : Gn g 1) (z : Kˣ), (z : K) = algebraMap (ZMod g) K ((y : Mt g 1) 0 0) →
      τ.character y = ((θ z : ℂˣ) : ℂ) := fun y z hz => by
    have := hf y (by rw [charpoly_fin_one]; exact irreducible_X_sub_C _) z (by
      rw [charpoly_fin_one]; simp [hz])
    simpa using this
  have hdim : Module.finrank ℂ τ = 1 := by
    have h1 := key 1 1 (by simp)
    rw [FDRep.char_one, map_one, Units.val_one] at h1
    exact_mod_cast h1
  rw [eq_trace_smul_of_finrank_one hdim (τ.ρ y) v]
  congr 1
  exact key y z hz

theorem lOneOf : LOneOf := by
  intro HT E E' Ω _ _ _ _ _ _ _ _ _ _ _ _ g _ A w h w' h' rc hrc i hi n hn hn1 hg hN a' ha' K _ _ red hr hk θ hθ τ
    hτ hf σ hs ξ hξ hξf
  subst hn1
  obtain ⟨a, ha, ε, hε, hL⟩ := hrc
  have : IsTotallyComplex E' := isTotallyComplex_of_algebra (E := E)
  have hgp : g.Prime := Fact.out

  obtain ⟨ω, -, hω⟩ := exists_smooth_hasCentralChar σ.smooth σ.irr
  have hωx : HasCentralChar (cls σ).rep ω := hasCentralChar_of_equiv (equivRep σ) hω

  have hωu : ∀ u : ℤ_[g]ˣ, ∀ U : (w.adicCompletion E)ˣ, (U : w.adicCompletion E) = i ((u : ℤ_[g]) : ℚ_[g]) →
      ∀ zc : Kˣ, (zc : K) = algebraMap (ZMod g) K (PadicInt.toZMod (u : ℤ_[g])) → (ω U : ℂ) = θ zc := by
    intro u U hU zc hzc
    obtain ⟨φ, hφ0, hφ⟩ := hs
    obtain ⟨v0, hv0⟩ : ∃ v0, φ v0 ≠ 0 := by
      by_contra hc
      exact hφ0 (LinearMap.ext fun v => not_not.1 fun hne => hc ⟨v, hne⟩)
    let k : GL (Fin 1) ℤ_[g] := GeneralLinearGroup.scalar (Fin 1) u
    have h1 := hφ k v0
    have hred : ((GlobalTheory.GLp.red g 1 k : Gn g 1) : Mt g 1) 0 0 = PadicInt.toZMod (u : ℤ_[g]) := by
      simp [k, GlobalTheory.GLp.red]
    rw [tau_scalar g K θ τ hf _ zc (by rw [hred, hzc]), map_smul] at h1
    have e : Matrix.GeneralLinearGroup.map i.toRingHom (GlobalTheory.GLp.inc g 1 k) = GeneralLinearGroup.scalar (Fin 1) U := by
      refine Units.ext (Matrix.ext fun a b => ?_)
      fin_cases a; fin_cases b
      simp [k, GlobalTheory.GLp.inc, hU]
    have h2 : (σ.ρ.comp (Matrix.GeneralLinearGroup.map i.toRingHom)) (GlobalTheory.GLp.inc g 1 k) (φ v0) = (ω U : ℂ) • φ v0 := by
      show σ.ρ (Matrix.GeneralLinearGroup.map i.toRingHom (GlobalTheory.GLp.inc g 1 k)) (φ v0) = _
      rw [e, hω U]
    rw [h2] at h1
    exact (smul_left_injective ℂ hv0 h1).symm

  have hNw : normV w = g := by rw [← resCard_eq_normV w, DiscreteGroups.sglob.DzIso.resCard_eq i hi]
  have hN' : normV w' = g := by rw [hN, pow_one]
  have hgw' := natCast_mem_of_normV w' g 1 Nat.one_pos hN
  have hgw : ((g : ℕ) : 𝓞 E) ∈ w.asIdeal := by
    refine (h _).1 ?_
    have e1 : algebraMap E Ω (((g : ℕ) : 𝓞 E) : E) = algebraMap E' Ω (((g : ℕ) : 𝓞 E') : E') := by simp
    rw [e1]
    exact (h' _).2 hgw'
  have hmap : ∀ y : 𝓞 E, y ∈ w.asIdeal → algebraMap (𝓞 E) (𝓞 E') y ∈ w'.asIdeal := fun y hy => by
    refine (h' _).1 ?_
    have e1 : algebraMap E' Ω ((algebraMap (𝓞 E) (𝓞 E') y : 𝓞 E') : E') = algebraMap E Ω (y : E) :=
      (IsScalarTower.algebraMap_apply E E' Ω (y : E)).symm
    rw [e1]
    exact (h y).2 hy
  have hgw2 : ((g : ℕ) : 𝓞 E) ∉ w.asIdeal ^ 2 := fun hm => hg (by
    have hle : Ideal.map (algebraMap (𝓞 E) (𝓞 E')) w.asIdeal ≤ w'.asIdeal := Ideal.map_le_iff_le_comap.2 hmap
    have h2 := Ideal.mem_map_of_mem (algebraMap (𝓞 E) (𝓞 E')) hm
    rw [Ideal.map_pow] at h2
    have := Ideal.pow_right_mono hle 2 h2
    rwa [map_natCast] at this)

  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  obtain ⟨π, hπ⟩ := IsAlgClosed.exists_pow_nat_eq ((g : ℕ) : Ω) (show 0 < g - 1 by have := hgp.two_le; omega)
  refine ⟨0, fun z => ?_⟩
  rw [pow_zero, pow_one]
  obtain ⟨t, x, hxz, hv⟩ := exists_ine_of_res g A w' h' 1 Nat.one_pos hN a' ha' K red hr hk z
  have hpol := hξf t x z hxz hv
  have htE := ine_restrict (E := E) t
  let s : Weil h := ineIncl h ⟨_, htE⟩
  rw [WD.inePol_of_mem_Ine _ htE] at hpol

  have hcard := WD.card_eig (rc (cls σ)) s
  rw [hL.dim] at hcard
  obtain ⟨α, hα⟩ := Multiset.card_eq_one.1 hcard
  have hprod := hL.central (cls σ) ω hωx s
  rw [hα, Multiset.prod_singleton] at hprod
  rw [WD.charPol_eq_prod, hα] at hpol
  simp only [Multiset.map_singleton, Multiset.prod_singleton, Finset.range_one, Finset.prod_singleton, pow_zero,
    pow_one] at hpol
  have hαξ : α = ((ξ z : ℂˣ) : ℂ) := by simpa using congrArg (Polynomial.eval 0) hpol
  have hξα : ((ξ z : ℂˣ) : ℂ) = α := hαξ.symm

  have hunit := GlobalTheory.ArtinInertia.isUnitAt_artin_ine h a ha ⟨_, htE⟩
  have hu1 : ‖i.symm (a s : w.adicCompletion E)‖ = 1 := by
    have hv1 : Valued.v (a s : w.adicCompletion E) = 1 := hunit
    have hle := (DiscreteGroups.sglob.DzIso.v_le_iff i hi (i.symm (a s : w.adicCompletion E))).1 (by
      rw [RingEquiv.apply_symm_apply, hv1])
    refine le_antisymm hle (not_lt.1 fun hlt => ?_)
    have := (DiscreteGroups.sglob.DzIso.v_lt_iff i hi (i.symm (a s : w.adicCompletion E))).2 hlt
    rw [RingEquiv.apply_symm_apply, hv1] at this
    exact lt_irrefl _ this
  let u : ℤ_[g]ˣ := PadicInt.mkUnits hu1
  have hu : (a s : w.adicCompletion E) = i ((u : ℤ_[g]) : ℚ_[g]) := by
    show _ = i (i.symm (a s : w.adicCompletion E))
    rw [RingEquiv.apply_symm_apply]

  obtain ⟨y, hy⟩ := GlobalTheory.unit_completion_approx_integer w (a s) hunit
  have hT' := HT E' Ω g A w' h' hgw' hg a' ha' π (by rw [hN']; exact hπ) t x hv
  have hT := HT E Ω g A w h hgw hgw2 a ha π (by rw [hNw]; exact hπ) ⟨_, htE⟩ y hy
  have hxy : A.valuation (algebraMap E' Ω (x : E') - algebraMap E Ω (y : E)) < 1 := by
    have e : algebraMap E' Ω (x : E') - algebraMap E Ω (y : E) =
        ((t : G E' Ω) π / π - algebraMap E Ω (y : E)) - ((t : G E' Ω) π / π - algebraMap E' Ω (x : E')) := by ring
    rw [e]
    exact lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt hT hT')
  set c : ZMod g := PadicInt.toZMod (u : ℤ_[g]) with hc
  have hym : y - (c.val : 𝓞 E) ∈ w.asIdeal := by
    have h1 : Valued.v (algebraMap E (w.adicCompletion E) ((y - (c.val : 𝓞 E) : 𝓞 E) : E)) < 1 := by
      have e : algebraMap E (w.adicCompletion E) ((y - (c.val : 𝓞 E) : 𝓞 E) : E) =
          -((a s : w.adicCompletion E) - algebraMap E (w.adicCompletion E) (y : E)) +
            i (((u : ℤ_[g]) : ℚ_[g]) - (c.val : ℚ_[g])) := by
        rw [map_sub, hu, map_natCast]
        push_cast
        ring
      rw [e]
      refine Valuation.map_add_lt _ (by rw [Valuation.map_neg]; exact hy) ?_
      refine (DiscreteGroups.sglob.DzIso.v_lt_iff i hi _).2 ?_
      have hk : (u : ℤ_[g]) - (c.val : ℤ_[g]) ∈ RingHom.ker (PadicInt.toZMod (p := g)) := by
        rw [RingHom.mem_ker, map_sub, map_natCast, ZMod.natCast_zmod_val, hc, sub_self]
      rw [PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits, PadicInt.norm_def,
        PadicInt.coe_sub, PadicInt.coe_natCast] at hk
      exact hk
    have h2 : w.valuation E ((y - (c.val : 𝓞 E) : 𝓞 E) : E) < 1 := by
      rw [← HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (R := 𝓞 E) w]
      exact h1
    exact (w.valuation_lt_one_iff_mem (K := E) _).1 h2
  have hA1 : A.valuation (algebraMap E Ω (y : E) - (c.val : Ω)) < 1 := by
    have := (h _).2 hym
    rw [show ((y - (c.val : 𝓞 E) : 𝓞 E) : E) = (y : E) - (c.val : E) by push_cast; ring, map_sub,
      map_natCast] at this
    exact this
  have hxm : x - (c.val : 𝓞 E') ∈ w'.asIdeal := by
    refine (h' _).1 ?_
    have e : algebraMap E' Ω ((x - (c.val : 𝓞 E') : 𝓞 E') : E') =
        (algebraMap E' Ω (x : E') - algebraMap E Ω (y : E)) + (algebraMap E Ω (y : E) - (c.val : Ω)) := by
      push_cast; ring
    rw [e]
    exact Valuation.map_add_lt _ hxy hA1
  have hzc : (z : K) = algebraMap (ZMod g) K c := by
    rw [← hxz]
    have := (RingHom.mem_ker.1 (hk ▸ hxm : x - (c.val : 𝓞 E') ∈ RingHom.ker red))
    rw [map_sub, map_natCast, sub_eq_zero] at this
    rw [this, ← map_natCast (algebraMap (ZMod g) K), ZMod.natCast_zmod_val]

  have hfin := hωu u (a s) hu z hzc
  refine Units.ext ?_
  rw [hξα, hprod]
  exact hfin

end DiscreteGroups.sglob.DzType
end
end

-- bundled from Development.DiscreteGroups.GlobalIrreducibility.FixedNeBotOfEquiv
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GLq
  GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Whittaker ValuativeRel

namespace DiscreteGroups.sglob.DzType

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem fixed_ne_bot_of_equiv' {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] {π : Representation ℂ G V} {σ : Representation ℂ G W} (φ : π.Equiv σ) {K : Subgroup G}
    (hπ : fixed π K ≠ ⊥) : fixed σ K ≠ ⊥ := by
  obtain ⟨v, hv, h0⟩ := (Submodule.ne_bot_iff _).1 hπ
  refine (Submodule.ne_bot_iff _).2 ⟨φ v, GlobalTheory.Parabolic.mem_fixed.2 fun u hu => ?_, fun h1 => h0 ?_⟩
  · exact (φ.toIntertwiningMap.isIntertwining _ _ u v).symm.trans
      (congrArg φ (GlobalTheory.Parabolic.mem_fixed.1 hv u hu))
  · exact φ.toLinearEquiv.injective (h1.trans (map_zero _).symm)

theorem isLower_iff {g m : ℕ} [Fact g.Prime] (b : Gn g m) :
    IsLower b ↔ (b : Mt g m).BlockTriangular OrderDual.toDual := Iff.rfl

def lowZ (g m : ℕ) [Fact g.Prime] : Subgroup (GL (Fin m) ℤ_[g]) where
  carrier := {x | IsLower (GlobalTheory.GLp.red g m x)}
  one_mem' := by
    show IsLower (GlobalTheory.GLp.red g m 1)
    rw [map_one, isLower_iff, Units.val_one]
    exact Matrix.blockTriangular_one
  mul_mem' := by
    intro x y hx hy
    show IsLower (GlobalTheory.GLp.red g m (x * y))
    rw [map_mul, isLower_iff, Units.val_mul]
    exact Matrix.BlockTriangular.mul hx hy
  inv_mem' := by
    intro x hx
    show IsLower (GlobalTheory.GLp.red g m x⁻¹)
    have : Invertible ((GlobalTheory.GLp.red g m x : Gn g m) : Mt g m) := (GlobalTheory.GLp.red g m x).invertible
    rw [map_inv, isLower_iff, Matrix.coe_units_inv]
    exact Matrix.blockTriangular_inv_of_blockTriangular hx

theorem toZMod_eq_zero_iff {g : ℕ} [Fact g.Prime] (x : ℤ_[g]) : PadicInt.toZMod x = 0 ↔ ‖(x : ℚ_[g])‖ < 1 := by
  rw [← RingHom.mem_ker, PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits,
    PadicInt.padic_norm_e_of_padicInt]

section Place

variable {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {g : ℕ} [Fact g.Prime]
  (i : ℚ_[g] ≃+* w.adicCompletion E) (hi : Continuous i)

def lowS (m : ℕ) : Subgroup (GL (Fin m) (w.adicCompletion E)) :=
  (lowZ g m).map ((Matrix.GeneralLinearGroup.map i.toRingHom).comp (GlobalTheory.GLp.inc g m))

theorem lowS_apply {m : ℕ} (x : GL (Fin m) ℤ_[g]) (a b : Fin m) :
    ((((Matrix.GeneralLinearGroup.map i.toRingHom).comp (GlobalTheory.GLp.inc g m)) x : GL (Fin m) (w.adicCompletion E)) :
      Matrix (Fin m) (Fin m) (w.adicCompletion E)) a b = i ((x : Matrix (Fin m) (Fin m) ℤ_[g]) a b : ℚ_[g]) := rfl

include hi

theorem lowS_one (m : ℕ) : KOne (w.adicCompletion E) (Fin m) ≤ lowS i m := by
  intro y hy
  obtain ⟨x, hx1, hx2⟩ := DiscreteGroups.sglob.DzIso.exists_of_mem_KOne i hi hy
  refine ⟨x, ?_, hx2⟩
  show IsLower (GlobalTheory.GLp.red g m x)
  rw [hx1, isLower_iff, Units.val_one]
  exact Matrix.blockTriangular_one

theorem lowS_KO (m : ℕ) : lowS i m ≤ KO (w.adicCompletion E) (Fin m) := by
  rintro _ ⟨x, -, rfl⟩
  exact DiscreteGroups.sglob.DzIso.map_inc_mem_KO i hi x

theorem lowS_upper (m : ℕ) : ∀ y ∈ lowS i m, ∀ a b, a < b →
    valuation (w.adicCompletion E) (((y : GL (Fin m) (w.adicCompletion E)) : Matrix (Fin m) (Fin m) _) a b) < 1 := by
  rintro _ ⟨x, hx, rfl⟩ a b hab
  rw [lowS_apply, DiscreteGroups.sglob.DzIso.valuation_lt_iff i hi, ← toZMod_eq_zero_iff]
  exact hx a b hab

theorem lowS_diag (m : ℕ) : ∀ y ∈ lowS i m, ∀ a,
    valuation (w.adicCompletion E) (((y : GL (Fin m) (w.adicCompletion E)) : Matrix (Fin m) (Fin m) _) a a) = 1 := by
  rintro _ ⟨x, hx, rfl⟩ a
  rw [lowS_apply]
  have hdet : ((GlobalTheory.GLp.red g m x : Gn g m) : Mt g m).det ≠ 0 := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply]
    exact Units.ne_zero _
  rw [Matrix.det_of_lowerTriangular _ hx] at hdet
  have hd : PadicInt.toZMod ((x : Matrix (Fin m) (Fin m) ℤ_[g]) a a) ≠ 0 :=
    (Finset.prod_ne_zero_iff.1 hdet) a (Finset.mem_univ a)
  rw [Ne, toZMod_eq_zero_iff] at hd
  refine le_antisymm ((DiscreteGroups.sglob.DzIso.valuation_le_iff i hi _).2 ?_) (not_lt.1 fun h => hd ?_)
  · rw [PadicInt.padic_norm_e_of_padicInt]; exact PadicInt.norm_le_one _
  · exact (DiscreteGroups.sglob.DzIso.valuation_lt_iff i hi _).1 h

theorem psi_of_lifts {ψ₀ : AddChar (ZMod g) Circle} {ψ : AddChar (w.adicCompletion E) Circle} (hL : Lifts1 i ψ₀ ψ) :
    ∀ y, valuation (w.adicCompletion E) y < 1 → ψ y = 1 := by
  intro y hy
  have hx : ‖i.symm y‖ < 1 := (DiscreteGroups.sglob.DzIso.valuation_lt_iff i hi (i.symm y)).1 (by simpa using hy)
  let z : ℤ_[g] := ⟨i.symm y, hx.le⟩
  have hz : PadicInt.toZMod z = 0 := (toZMod_eq_zero_iff z).2 hx
  have h := hL z
  rw [hz, AddChar.map_zero_eq_one] at h
  have e : i (z : ℚ_[g]) = y := by simp [z]
  rwa [e] at h

end Place

theorem lGen : LGen := by
  intro H E _ _ w g _ i hi ψ₀ _ ψ hψc hL m
  obtain ⟨hirr, hsph, hcen⟩ := genA H (w.adicCompletion E) m
  let τ₀ : IrrRep (GL (Fin m) (w.adicCompletion E)) :=
    ⟨PS (w.adicCompletion E) m, psOne (w.adicCompletion E) m, isSmooth_parInd _ _, hirr⟩
  refine ⟨τ₀, 1, ?_, hcen, ?_⟩
  · obtain ⟨φ⟩ := IrrRep.nonempty_equiv_rep τ₀
    exact fixed_ne_bot_of_equiv' φ.symm hsph
  · obtain ⟨l, hl, hlv⟩ := exists_cell_functional (lowS_one i hi m) (lowS_KO i hi m) (lowS_upper i hi m)
      (lowS_diag i hi m) ψ hψc (psi_of_lifts i hi hL)
    exact ⟨l, cellVec (lowS_one i hi m) (lowS_diag i hi m), hl, hlv, fun x hx =>
      cellVec_fixed (lowS_one i hi m) (lowS_diag i hi m) ⟨x, hx, rfl⟩⟩

end DiscreteGroups.sglob.DzType
end
end

-- bundled from Development.DiscreteGroups.GlobalIrreducibility.IsRowFixConj
section
noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

open GlobalTheory.GLq GlobalTheory.Whittaker GlobalTheory.SmGL Matrix
open scoped Classical

namespace DiscreteGroups.sglob.DzFe

variable {g : ℕ} [Fact g.Prime] {m : ℕ}

theorem sd_eq (A : Gn g (m + 1)) :
    superDiag A = ∑ l : Fin m, (A : Mt g (m + 1)) (Fin.castSucc l) (Fin.succ l) := by
  unfold superDiag
  simp_rw [Finset.sum_filter]
  rw [Fin.sum_univ_castSucc]
  rw [Finset.sum_eq_zero (fun k _ => if_neg (by have := k.2; simp only [Fin.val_last]; omega)), add_zero]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [Finset.sum_eq_single (Fin.succ l)]
  · simp
  · intro b _ hb
    rw [if_neg]
    intro h
    exact hb (Fin.ext (by simp [h]))
  · simp

theorem trace_phi (j : ℕ) (p : (SIdx m → ZMod g) × (ZMod g)ˣ × (WIdx m j → ZMod g)) :
    trace ((phi j p : Gn g (m + 1)) : Mt g (m + 1)) - ((phi j p : Gn g (m + 1)) : Mt g (m + 1)) 0 0 =
      superDiag (umGL p.1) := by
  rw [phi_val]
  simp only [Matrix.trace, Matrix.diag, cyc_mul_apply]
  rw [← Equiv.sum_comp (finRotate (m + 1))]
  simp only [Equiv.symm_apply_apply]
  rw [Fin.sum_univ_castSucc, finRotate_last, rot_symm_zero, add_sub_cancel_right, sd_eq, umGL_val]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [rot_castSucc, hp_um_row _ _ _ (Fin.castSucc_lt_last l).ne]

theorem isRowFix_conj {j : ℕ} (r : Fin (m + 1) → ZMod g) (hr : ∀ l : Fin (m + 1), (l : ℕ) ≤ j → r l = 0)
    (hr0 : r (Fin.last m) ≠ 0) : IsRowFix j (cyc g (m + 1) * hpGL r hr0 * (cyc g (m + 1))⁻¹) := by
  have he : ∀ i k, ((cyc g (m + 1) * hpGL r hr0 * (cyc g (m + 1))⁻¹ : Gn g (m + 1)) : Mt g (m + 1)) i k =
      Hp r ((finRotate (m + 1)).symm i) ((finRotate (m + 1)).symm k) := fun i k => by
    rw [Units.val_mul, Units.val_mul, mul_cycinv_apply, cyc_mul_apply, hpGL_val]
  refine ⟨fun i k hi => ?_, fun i k hi hk0 hk => ?_⟩
  · have hi' : i ≠ 0 := fun h => hi (by simp [h])
    rw [he]
    simp only [Hp, Matrix.of_apply, if_neg (rot_symm_ne_last i hi'), Matrix.one_apply,
      (finRotate (m + 1)).symm.apply_eq_iff_eq]
  · have hi' : i = 0 := Fin.ext hi
    have hk' : k ≠ 0 := fun h => by simp [h] at hk0
    subst hi'
    rw [he, rot_symm_zero]
    simp only [Hp, Matrix.of_apply, if_pos rfl]
    have hv := rot_symm_val k hk'
    exact hr _ (by omega)

theorem phi_inj {j : ℕ} {p q : (SIdx m → ZMod g) × (ZMod g)ˣ × (WIdx m j → ZMod g)} (h : phi j p = phi j q) :
    p = q := by
  obtain ⟨N1, t1, w1⟩ := p
  obtain ⟨N2, t2, w2⟩ := q
  unfold phi at h
  rw [mul_assoc, mul_assoc] at h
  have h1 := mul_left_cancel h
  have hz := congrArg (fun A : Gn g (m + 1) => (A : Mt g (m + 1))) h1
  simp only [Units.val_mul, hpGL_val, umGL_val] at hz
  have hN : N1 = N2 := by
    funext q
    have hne : q.1.1 ≠ Fin.last m := ne_of_lt (lt_of_lt_of_le q.2 (Fin.le_last _))
    have := congrFun (congrFun hz q.1.1) q.1.2
    rw [hp_um_row _ _ _ hne, hp_um_row _ _ _ hne] at this
    simpa [Um, ne_of_lt q.2, q.2] using this
  subst hN
  have h2 := mul_right_cancel h1
  have hr : ∀ k, rvec j t1 w1 k = rvec j t2 w2 k := fun k => by
    have := congrArg (fun A : Gn g (m + 1) => (A : Mt g (m + 1)) (Fin.last m) k) h2
    simpa [hpGL_val, Hp] using this
  have ht : t1 = t2 := Units.ext (by simpa [rvec_last] using hr (Fin.last m))
  have hw : w1 = w2 := by
    funext q
    have hq : q.1 ≠ Fin.last m := fun e => by
      have := q.2.2
      rw [e, Fin.val_last] at this
      omega
    simpa [rvec, hq, q.2] using hr q.1
  rw [ht, hw]

end DiscreteGroups.sglob.DzFe
end
end

-- bundled from Development.DiscreteGroups.GlobalIrreducibility.KUSStable
section
noncomputable section

set_option linter.unusedSectionVars false
set_option linter.deprecated false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.unusedSimpArgs false

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.Whittaker Matrix DiscreteGroups.sglob.LConvGenM

namespace DiscreteGroups.sglob.LConvGenR

variable {k : Type} [Field k] {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
variable (π : Representation ℂ (GL (Fin n) k) V) (ψ : AddChar k Circle)

def chM (m : ℕ) (g : GL (Fin n) k) : ℂ := ((ψ (sdS m (g : Matrix (Fin n) (Fin n) k)) : Circle) : ℂ)

def KN (m : ℕ) : Submodule ℂ V :=
  Submodule.span ℂ {w | ∃ g ∈ Nset m, ∃ v : V, w = π g v - chM ψ m g • v}

def KUS (j : ℕ) (S : Finset (Fin n)) (ξ : Fin n → k) : Submodule ℂ V :=
  Submodule.span ℂ {w | ∃ c : Fin n → k, (∀ r ∉ S, c r = 0) ∧ ∃ v : V,
    w = π (colU j c) v - ((ψ (dotj j ξ c) : Circle) : ℂ) • v}

theorem conj_apply (x g : GL (Fin n) k) (v : V) : π x (π g v) = π (x * g * x⁻¹) (π x v) := by
  rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right]

theorem KN_stable (j : ℕ) (x : GL (Fin n) k) (hx : Good j (x : Matrix (Fin n) (Fin n) k))
    (hy : Good j ((x⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)) {w : V} (hw : w ∈ KN π ψ (j + 1)) :
    π x w ∈ KN π ψ (j + 1) := by
  refine (Submodule.span_le.2 ?_ : KN π ψ (j + 1) ≤ (KN π ψ (j + 1)).comap (π x)) hw
  rintro _ ⟨g, hg, v, rfl⟩
  obtain ⟨h1, h2⟩ := good_conj x hx hy hg
  refine Submodule.subset_span ⟨x * g * x⁻¹, h1, π x v, ?_⟩
  rw [map_sub, map_smul, conj_apply, chM, chM, h2]

theorem colU_comm (j : ℕ) (c d : Fin n → k) : colU j c * colU j d = colU j d * colU j c := by
  rw [← colU_add, ← colU_add, add_comm]

theorem KUS_stable (j : ℕ) (S : Finset (Fin n)) (ξ d : Fin n → k) {w : V} (hw : w ∈ KUS π ψ j S ξ) :
    π (colU j d) w ∈ KUS π ψ j S ξ := by
  refine (Submodule.span_le.2 ?_ : KUS π ψ j S ξ ≤ (KUS π ψ j S ξ).comap (π (colU j d))) hw
  rintro _ ⟨c, hc, v, rfl⟩
  refine Submodule.subset_span ⟨c, hc, π (colU j d) v, ?_⟩
  rw [map_sub, map_smul, ← Module.End.mul_apply, ← map_mul, colU_comm, map_mul, Module.End.mul_apply]

theorem W_stable (j : ℕ) (S : Finset (Fin n)) (ξ d : Fin n → k) {w : V}
    (hw : w ∈ KN π ψ (j + 1) ⊔ KUS π ψ j S ξ) : π (colU j d) w ∈ KN π ψ (j + 1) ⊔ KUS π ψ j S ξ := by
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hw
  rw [map_add]
  exact Submodule.add_mem_sup (KN_stable π ψ j _ (good_colU j d) (good_colU_inv j d) ha)
    (KUS_stable π ψ j S ξ d hb)

theorem KN_top (m : ℕ) (hm : n ≤ m) : KN π ψ m = ⊥ := by
  refine Submodule.span_eq_bot.2 ?_
  rintro _ ⟨g, hg, v, rfl⟩
  have hg1 : g = 1 := by
    ext i l
    rw [hg i l (Or.inr (by omega)), Units.val_one]
  have hs : sdS m ((1 : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) = 0 := by
    refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun l _ => ?_
    rw [if_neg (by omega)]
  rw [hg1, chM, hs, AddChar.map_zero_eq_one, Circle.coe_one, one_smul, map_one, Module.End.one_apply, sub_self]

end DiscreteGroups.sglob.LConvGenR
end
end

