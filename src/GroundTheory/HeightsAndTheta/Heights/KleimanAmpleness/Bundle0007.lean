import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.AlgebraMapMemChartRingLine
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.StatementsSerrePoly
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.EqZeroOrIsHomogeneousOfMemPolyPiece
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0004

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.BaseChangeObj
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

noncomputable section

universe u u' w

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}

def SubSystem.baseChange (O : Type u') [CommRing O] [Algebra O Ω] (Q : SubSystem S x Ω) : SubSystem O x Ω where
  sub I := Submodule.span (chartRing O x I) (Q.sub I : Set Ω)
  mono I₁ I₂ h z hz := by
    refine Submodule.span_induction
      (p := fun z _ => z ∈ Submodule.span (chartRing O x I₂) (Q.sub I₂ : Set Ω)) ?_ ?_ ?_ ?_ hz
    · intro z hz; exact Submodule.subset_span (Q.mono I₁ I₂ h z hz)
    · exact Submodule.zero_mem _
    · intro a b _ _ ha hb; exact Submodule.add_mem _ ha hb
    · intro a z _ hz; exact Submodule.smul_mem _ (chartIncl h a) hz

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.CechPartitionSt
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

noncomputable section

universe u v w

def CechPartition.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] (Ω : Type w) [Field Ω] (E : Type v) [AddCommGroup E] [Module Ω E] [Module S E]
    {n : ℕ} (U : Finset (Fin n)) (M : Cell U → Submodule S E) (m : ℕ) (a b : Fin m → Ω) (j : Fin m → Fin n),
    (∀ k, j k ∈ U) → ∑ k, a k * b k = 1 →
    (∀ k I, ∀ z ∈ M I, a k • z ∈ M I) → (∀ k I, ∀ z ∈ M I, b k • z ∈ M I) →
    (∀ k (I I' : Cell U), I'.1 = insert (j k) I.1 → ∀ z ∈ M I', ∃ e : ℕ, b k ^ e • z ∈ M I) →
    ∀ p : ℕ, ∀ s ∈ Cech.Cdeg (fun _ : Cell U => E) M (p + 1),
      Cech.d (fun _ : Cell U => E) (Cech.idRes S E U) (p + 1) s = 0 →
        ∃ t ∈ Cech.Cdeg (fun _ : Cell U => E) M p, Cech.d (fun _ : Cell U => E) (Cech.idRes S E U) p t = s

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.CutDimLowerSt
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

def CutDimLower.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (n : ℕ) (pp : Ideal (Poly k N)) (L : LineBundle k x) (s : Ω) (qq : Ideal (Poly k N)),
    IsSubvar x pp (n + 1) → s ∈ L.secs → qq ∈ (pp ⊔ zeroIdeal L.toSubSystem s).minimalPrimes →
    (∃ j, (X j : Poly k N) ∉ qq) → ((n + 1 : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (Poly k N ⧸ qq)

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.CutMultPosSt
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

noncomputable section

universe u

def CutMultPos.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] [IsNoetherianRing S] (N : ℕ) (J qq : Ideal (Poly S N))
    (h : qq ∈ J.minimalPrimes),
    haveI : qq.IsPrime := h.1.1
    0 < cutMult J qq ∧ cutMult J qq < ⊤

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.CycleSplitFiltStepSt
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial Filter

noncomputable section

universe u w

def CycleSplit.Filt.Step.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] [IsNoetherianRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ)
    (x : Fin (N + 1) → Ω) (𝔪 : Ideal S), 𝔪.IsMaximal →
    ∀ (K pp : Ideal (Poly S N)) (g : Poly S N) (e : ℕ),
    (∀ f ∈ K, ∀ d : ℕ, homogeneousComponent d f ∈ K) → primeOf (S := S) x ≤ K →
    𝔪.map (C : S →+* Poly S N) ≤ K → g.IsHomogeneous e →
    (∀ f ∈ pp, ∀ d : ℕ, homogeneousComponent d f ∈ pp) → (∀ f, f ∈ pp ↔ f * g ∈ K) →
    ∀ Q : LineBundle S x, ∀ᶠ c : ℕ in atTop,
      restrLen K (Q.twist (twistSys S x (c : ℤ))) =
        restrLen (K ⊔ Ideal.span {g}) (Q.twist (twistSys S x (c : ℤ))) +
          restrLen pp (Q.twist (twistSys S x ((c : ℤ) - e)))

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.GlobalFunctionsIntegralSt
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

def GlobalFunctionsIntegral.Statement : Prop :=
  ∀ (k : Type u) [Field k] (K : Type w) [Field K] [Algebra k K] (N : ℕ) (y : Fin (N + 1) → K) (a : K),
    y ≠ 0 → (∀ (i : Fin (N + 1)) (hi : y i ≠ 0), a ∈ chartRing k y (singleChart hi)) → IsIntegral k a

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsBisAltAlt
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.TranslateEq

open MvPolynomial

def LineBundle.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (N : ℕ) (Ω : Type) [Field Ω] [Algebra S Ω] (x : Fin (N + 1) → Ω),
    (∀ Q : Kleiman.LineBundle S x,
      ∃ Q' : IndefiniteRowSideFullHecke.Kleiman.LineBundle (S := S) x, ∀ i, Q'.mods i = toIndefiniteRowSideFullHecke Q.toSubSystem i) ∧
    ∀ Q' : IndefiniteRowSideFullHecke.Kleiman.LineBundle (S := S) x,
      ∃ Q : Kleiman.LineBundle S x, ∀ i, x i ≠ 0 → Q'.mods i = toIndefiniteRowSideFullHecke Q.toSubSystem i

end GroundTheory.Heights₂.Heights.Kleiman.TranslateEq
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsBisAltBis
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.TranslateEq

open MvPolynomial

def GradedCech.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (N : ℕ),
    ∃ e : ∀ (M : Type) [AddCommGroup M] [Module (Poly S N) M] [Module S M] [IsScalarTower S (Poly S N) M]
        (G : IndefiniteRowSideFullHecke.Kleiman.GradedMod S N M) (i : ℕ) (c : ℤ),
        IndefiniteRowSideFullHecke.Kleiman.gradedH S N M G i c ≃ₗ[S] Kleiman.cohom (gradedEquiv S N M G) i c,
      (∀ (M M' : Type) [AddCommGroup M] [Module (Poly S N) M] [Module S M] [IsScalarTower S (Poly S N) M]
        [AddCommGroup M'] [Module (Poly S N) M'] [Module S M'] [IsScalarTower S (Poly S N) M']
        (G : IndefiniteRowSideFullHecke.Kleiman.GradedMod S N M) (G' : IndefiniteRowSideFullHecke.Kleiman.GradedMod S N M')
        (f : M →ₗ[Poly S N] M') (hf : IndefiniteRowSideFullHecke.Kleiman.IsGradedHom S N G G' f) (i : ℕ) (c : ℤ)
        (z : IndefiniteRowSideFullHecke.Kleiman.gradedH S N M G i c),
        e M' G' i c (IndefiniteRowSideFullHecke.Kleiman.gradedHmap S N hf i c z) =
          Kleiman.cohomMap (⟨f, fun c m hm => hf c m hm⟩ :
            Kleiman.GradedHom (gradedEquiv S N M G) (gradedEquiv S N M' G')) i c (e M G i c z)) ∧
      ∀ (M : Type) [AddCommGroup M] [Module (Poly S N) M] [Module S M] [IsScalarTower S (Poly S N) M]
        (G : IndefiniteRowSideFullHecke.Kleiman.GradedMod S N M) (c : ℤ) (m : M) (hm : m ∈ G.piece c)
        (z : IndefiniteRowSideFullHecke.Kleiman.gradedZ S N M G 0 c),
        (z : ∀ I, (IndefiniteRowSideFullHecke.Kleiman.gradedSys S N M G c).V I) = IndefiniteRowSideFullHecke.Kleiman.unitCochain S N M m →
        e M G 0 c (Submodule.Quotient.mk z) = Kleiman.toH0 (gradedEquiv S N M G) c ⟨m, hm⟩

end GroundTheory.Heights₂.Heights.Kleiman.TranslateEq
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsBisFurther
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

def CellDSq.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type) [∀ k, Fintype (ι k)]
    [∀ k, LinearOrder (ι k)] (Ω : Type) [Field Ω] [Algebra S Ω] (y : (Σ k, ι k) → Ω) (n : ℕ)
    (s : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell K ι n → Ω), cellD S y (n + 1) (cellD S y n s) = 0

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsLastLast
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.TranslateEq

open MvPolynomial

def Ample.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (N : ℕ) (Ω : Type) [Field Ω] [Algebra S Ω] (x : Fin (N + 1) → Ω)
    (H : Kleiman.LineBundle S x), Kleiman.AmpleData S x H →
    Nonempty (IndefiniteRowSideFullHecke.Kleiman.AmpleData S x (toIndefiniteRowSideFullHecke H.toSubSystem))

noncomputable def Ample.hyps (k : Type) [Field k] :
    Kleiman.AmpleData k (Kleiman.lineX k) (Kleiman.twistBundle k (Kleiman.lineX k) 1) :=
  Kleiman.twistAmple k (Kleiman.lineX k)

end GroundTheory.Heights₂.Heights.Kleiman.TranslateEq
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsRestLast
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial

def RestrictGen.Statement : Prop :=
  ∀ (F : Type) [Field F] (N : ℕ) (Ω : Type) [Field Ω] [Algebra F Ω] (x : Fin (N + 1) → Ω)
    (K' : Type) [Field K'] [Algebra F K'] (x' : Fin (N + 1) → K') (hxy : ∀ i, x' i ≠ 0 → x i ≠ 0)
    (R : Subalgebra F Ω) (σ : R →ₐ[F] K'),
    (∀ (f g : Kleiman.Poly F N) (m : ℕ), f.IsHomogeneous m → g.IsHomogeneous m → aeval x' g ≠ 0 →
      ∃ h : aeval x f / aeval x g ∈ R, σ ⟨_, h⟩ = aeval x' f / aeval x' g) →
    ∀ (Q : Kleiman.LineBundle F x) (Q' : Kleiman.LineBundle F x') (c : ℤ) (H : Set Ω) (ρ : Ω → K') (w : Ω)
      (w' : K'), w' ≠ 0 →
      (∀ I, (Q.toSubSystem.twist (Kleiman.twistSys F x c)).sub I = Submodule.span (Kleiman.chartRing F x I) H) →
      (∀ I, (Q'.toSubSystem.twist (Kleiman.twistSys F x' c)).sub I =
        Submodule.span (Kleiman.chartRing F x' I) (ρ '' H)) →
      (∀ h ∈ H, ∃ hh : h * w ∈ R, σ ⟨_, hh⟩ = ρ h * w') →
      ∃ r : Ω → K', Kleiman.RestrictData Q.toSubSystem hxy Q'.toSubSystem r

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.LeadingCoeffPosSt
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

noncomputable section

universe u w

def LeadingCoeffPos.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω) (d : ℕ)
    (M Nb : LineBundle k x) (q : ℕ) (m : ℤ) (b : ℕ), IsSubvar x (primeOf (S := k) x) (d + 1) →
    Nef M.toSubSystem → Nb.toSubSystem = twistMul M.toSubSystem q m → IsVeryAmple Nb.toSubSystem →
    ((d + 1 : ℕ) : ℤ) * b < m →
    0 < interNum (primeOf (S := k) x) (fun _ : Fin (d + 1) => Nb.toSubSystem) -
          ((d + 1 : ℕ) : ℤ) * interNum (primeOf (S := k) x)
            (Fin.cons (α := fun _ => SubSystem k x Ω) (twistSys k x (b : ℤ))
              (fun _ : Fin d => Nb.toSubSystem))

end

end GroundTheory.Heights₂.Heights.Kleiman
end

