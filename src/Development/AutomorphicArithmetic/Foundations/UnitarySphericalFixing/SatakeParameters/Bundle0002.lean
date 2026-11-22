import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.AbsCentral
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.Multi
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.ClBasic
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.SwOn
import Development.DiscreteGroups.GlobalIrreducibility.DzMatchCut
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007

-- bundled from Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.GoodLem
section
noncomputable section

open ValuativeRel GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.LocLanglands UpperTheory.Zero.LLC

namespace UpperTheory.One.M

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def IsQg (k : Type) [Field k] [TopologicalSpace k] : Prop := ∃ (g : ℕ) (_ : Fact g.Prime) (i : ℚ_[g] ≃+* k), Continuous i

theorem good_ofChar (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ) : Good (IrrGL.ofChar χ hχ) :=
  ⟨{IrrGL.ofChar χ hχ}, hasSupport_self (IrrGL.isCusp_ofChar χ hχ), fun y hy => by
    rw [Multiset.mem_singleton.1 hy]
    exact Or.inl rfl⟩

theorem good_of_toral {x : IrrGL k} (h : Toral x) : Good x :=
  let ⟨s, hs, h1⟩ := h
  ⟨s, hs, fun y hy => Or.inl (h1 y hy)⟩

variable [CharZero k]

theorem good_of_one (x : IrrGL k) (h : x.1 = 1) : Good x := by
  obtain ⟨χ, hχ, rfl⟩ := ((clBasic k x).2.2.2.2.1 h).2
  exact good_ofChar χ hχ

theorem good_of_fixed (hq : IsQg k) (x : IrrGL k) (hD : fixed x.rep (KOne k (Fin x.1)) ≠ ⊥) : Good x := by
  obtain ⟨s, hs⟩ := GlobalTheory.LocGL.SupportRing.exists_hasSupport Pr.zel x
  refine ⟨s, hs, fun y hy => Or.inr ⟨hq, y, 1, isSmoothChar_one, ?_, ((clBasic k y).2.2.1 _).symm⟩⟩
  obtain ⟨n, xs, hxs, hcs⟩ := hs
  have H := Pr.dzs _ x.1 (GlobalTheory.SplitRead.Irr.ofIrrRep x.2.rep) n (fun i => (xs i).1)
    (fun i => GlobalTheory.SplitRead.Irr.ofIrrRep (xs i).2.rep) hcs ((Submodule.ne_bot_iff _).1 hD)
  rw [← hxs] at hy
  obtain ⟨i, -, rfl⟩ := Multiset.mem_map.1 hy
  obtain ⟨v, hv, hv0⟩ := H i
  exact (Submodule.ne_bot_iff _).2 ⟨v, hv, hv0⟩

theorem good_cls_of_fixed (hq : IsQg k) {n : ℕ} (τ : IrrRep (GL (Fin n) k)) (hD : fixed τ.ρ (KOne k (Fin n)) ≠ ⊥) :
    Good (cls τ) :=
  good_of_fixed hq _ (fixed_ne_bot_of_equiv (IrrRep.nonempty_equiv_rep τ).some.symm hD)

section Close

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne GlobalTheory.Published

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
  {a : Weil h →* (w.adicCompletion E)ˣ} {ha : IsLocalArtin h a} {ε : EpsFamily A} {rc : IrrGL (w.adicCompletion E) → WD h}

theorem charZero_compl (w : HeightOneSpectrum (𝓞 E)) : CharZero (w.adicCompletion E) :=
  charZero_of_injective_algebraMap (algebraMap E _).injective

theorem Old.close (hε : IsDeligneEps ε) (H : Laws a ha ε rc) : IsRec h rc := ⟨a, ha, ε, hε, H⟩

theorem New.close (H : LawsM a ha ε rc) : IsRecT h rc := cls_of H

theorem Old.artin (hL : LocalLanglandsGL) (h : IsPlaceOver A w) : ∃ a : Weil h →* (w.adicCompletion E)ˣ, IsLocalArtin h a :=
  let ⟨_, ⟨a, ha, _⟩, _⟩ := hL.1 E Ω A w h
  ⟨a, ha⟩

theorem New.artin (hL : RecTExists) (h : IsPlaceOver A w) : ∃ a : Weil h →* (w.adicCompletion E)ˣ, IsLocalArtin h a :=
  let ⟨_, a, ha, _⟩ := hL E Ω A w h
  ⟨a, ha⟩

end Close

end UpperTheory.One.M
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.Narrow
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands UpperTheory.Zero.LLC

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.One.M

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w} {rc : IrrGL (w.adicCompletion E) → WD h}

theorem Old.typeS (s : Sw) (_H : IsRec h rc) : TypeLaw h rc := s.elim

theorem New.typeS (_s : TrivialCondition) (H : IsRecT h rc) : TypeLaw h rc := H.choose_spec.choose_spec.type

theorem narrowBig (s : Sw) (_art : GlobalTheory.Published.GlobalArtinReciprocity) (_hL : GlobalTheory.Published.LocalLanglandsGL) :
    DiscreteGroups.sglob.DzType.NarrowBig :=
  fun _ E' _ _ _ _ _ _ _ _ _ _ _ _ _ g _ _ _ _ w' h' _ H i hi n hn _ h1 h2 a' ha' K _ _ red h3 h4 θ hθ τ hτ h5 σ h6 =>
    (Old.typeS s H E' g w' h' i hi n hn h1 h2 a' ha' K red h3 h4 θ hθ τ hτ h5 σ h6).2

end UpperTheory.One.M
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.RecLawsH
section
noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands UpperTheory.Zero.LLC GlobalTheory.Published GlobalTheory.SplitRead

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.One.M

section Laws

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

def GoodI {n : ℕ} (π : Irr k n) : Prop := Good (cls (⟨π.V, π.π, π.smooth, π.irr⟩ : IrrRep (GL (Fin n) k)))

structure RecLawsH (rc : ∀ n, Irr k n → WD h) : Prop where
  dim : ∀ n π, (rc n π).lpDim = n
  iso : ∀ n (π π' : Irr k n), GoodI π' → (rc n π = rc n π' ↔ Nonempty (π.π.Equiv π'.π))
  isoMp : ∀ n (π π' : Irr k n), Nonempty (π.π.Equiv π'.π) → rc n π = rc n π'
  prod : ∀ r t (σ : Irr k r) (τ : Irr k t) (π : Irr k (r + t)),
    Nonempty (π.π.Equiv (prod₂ σ.π τ.π)) → rc (r + t) π = (rc r σ).lpSum (rc t τ)
  det : ∀ t (χ : kˣ →* ℂˣ) (c : Irr k 1) (τ : Irr k t),
    Nonempty (c.π.Equiv (detRep (Fin 1) χ)) → Nonempty (τ.π.Equiv (detRep (Fin t) χ)) → rc t τ = speh (rc 1 c) t
  twist : ∀ n (χ : kˣ →* ℂˣ) (c : Irr k 1) (π π' : Irr k n),
    GoodI π → Nonempty (c.π.Equiv (detRep (Fin 1) χ)) →
    Nonempty (π'.π.Equiv (twist π.π (detChar (Fin n) χ))) → rc n π' = (rc n π).lpChar (rc 1 c)
  sph : ∀ n (π : Irr k n), (rc n π).unr ↔ IsSpherical π.π
  sat : ∀ n (π : Irr k n) (α : Fin n → ℂˣ), HasSatake π.π α →
    (rc n π).frobEig = Finset.univ.val.map fun i => ((α i)⁻¹ : ℂˣ).1

theorem Old.rlIso {rc : ∀ n, Irr k n → WD h} (H : RecLaws rc) : ∀ n (π π' : Irr k n), GoodI π' →
    (rc n π = rc n π' ↔ Nonempty (π.π.Equiv π'.π)) := fun n π π' _ => H.iso n π π'

theorem Old.rlIsoMp {rc : ∀ n, Irr k n → WD h} (H : RecLaws rc) : ∀ n (π π' : Irr k n), Nonempty (π.π.Equiv π'.π) →
    rc n π = rc n π' := fun n π π' => (H.iso n π π').2

theorem Old.rlTwist {rc : ∀ n, Irr k n → WD h} (H : RecLaws rc) : ∀ n (χ : kˣ →* ℂˣ) (c : Irr k 1) (π π' : Irr k n),
    GoodI π → Nonempty (c.π.Equiv (detRep (Fin 1) χ)) →
    Nonempty (π'.π.Equiv (GlobalTheory.SmGL.twist π.π (detChar (Fin n) χ))) → rc n π' = (rc n π).lpChar (rc 1 c) :=
  fun n χ c π π' _ => H.twist n χ c π π'

theorem recLawsH {rc : IrrGL (w.adicCompletion E) → WD h} (H : IsRec h rc) :
    RecLawsH fun _ (π : Irr (w.adicCompletion E) _) => rc (cls (toIrrRep π)) := by
  obtain ⟨a, ha, ε, -, H⟩ := H
  have hc : ∀ (χ : (w.adicCompletion E)ˣ →* ℂˣ) (c : Irr (w.adicCompletion E) 1),
      Nonempty (c.π.Equiv (detRep (Fin 1) χ)) → ∃ hχ : IsSmoothChar χ, cls (toIrrRep c) = .ofChar χ hχ := by
    rintro χ c ⟨φ⟩
    have h1 : IsSmoothChar (detChar (Fin 1) χ) := (isSmooth_ofChar_iff _).1
      ((IsSubquotient.of_surjective φ.toIntertwiningMap φ.toLinearEquiv.surjective).isSmooth c.smooth)
    have h2 : Continuous (Matrix.GeneralLinearGroup.scalar (R := w.adicCompletion E) (Fin 1)) :=
      Units.continuous_map (continuous_matrix fun i j => by
        rw [Subsingleton.elim i j]; simpa using continuous_id')
    have h3 : (detChar (Fin 1) χ).comp (Matrix.GeneralLinearGroup.scalar (Fin 1)) = χ := by
      refine MonoidHom.ext fun z => congrArg χ ?_
      ext; simp [Matrix.GeneralLinearGroup.scalar]
    exact ⟨h3 ▸ h1.comp _ h2, congrArg (Sigma.mk 1) (IrrRep.cl_eq_iff.2 ⟨φ⟩)⟩
  have hmp : ∀ n (π π' : IrrRep (GL (Fin n) (w.adicCompletion E))), Nonempty (π.ρ.Equiv π'.ρ) → cls π = cls π' :=
    fun n π π' e => congrArg (Sigma.mk n) (IrrRep.cl_eq_iff.2 e)
  refine ⟨fun n π => H.dim _, fun n π π' hg => ⟨fun e => ?_, fun e => congrArg rc (hmp n _ _ e)⟩,
    fun n π π' e => congrArg rc (hmp n _ _ e), fun r t σ τ π hπ => H.prod r t _ _ _ hπ, ?_, ?_, ?_, ?_⟩
  · have := Old.inj H _ _ hg e
    exact IrrRep.cl_eq_iff.1 (eq_of_heq (Sigma.mk.inj this).2)
  · intro t χ c τ h1 h2
    obtain ⟨hχ, e⟩ := hc χ c h1
    rw [e, congrArg rc (hmp t (toIrrRep τ) (IrrRep.det (Fin t) χ hχ) h2), H.det, sumList, List.foldr_map, speh]
    simp [List.foldr_map, ← List.map_eq_flatMap]
  · intro n χ c π π' hg h1 h2
    obtain ⟨hχ, e⟩ := hc χ c h1
    rw [e, ← Old.twist H (cls (toIrrRep π)) χ hχ hg]
    exact congrArg rc ((IrrGL.of_eq_of.2 h2).trans (IrrGL.tw_of π.π π.smooth π.irr χ hχ).symm)
  · intro n π
    rw [← H.sph]
    exact ⟨fixed_ne_bot_of_equiv (equivRep (toIrrRep π)).symm, fixed_ne_bot_of_equiv (equivRep (toIrrRep π))⟩
  · intro n π α hα
    have φ := equivRep (toIrrRep π)
    rw [H.sat (cls (toIrrRep π)) α ⟨IrrRep.irr _, fixed_ne_bot_of_equiv φ hα.2.1,
      (IsSubquotient.of_surjective φ.toIntertwiningMap φ.toLinearEquiv.surjective).trans hα.2.2⟩, WD.frobEig_diag]

end Laws

end UpperTheory.One.M
end
end

