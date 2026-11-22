import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.AlgDefs
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.CoordIdealIsMultiProjPrime
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0003

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.CellMeets
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

variable (S : Type) [CommRing S] {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type}
  [Field Ω] [Algebra S Ω]

def CellMeets (y : (Σ k, ι k) → Ω) (I : ∀ k, Finset (ι k)) : Prop :=
  ∀ k, ∀ i ∈ I k, y ⟨k, i⟩ ≠ 0

open Classical in

def cellSec (y : (Σ k, ι k) → Ω) (γ : K → ℤ) (I : ∀ k, Finset (ι k)) : Submodule S Ω :=
  if CellMeets y I then
    Submodule.span S {z | ∃ (g t : MRingOver S ι) (a : K → ℕ),
      t ∈ ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.cellMon S I ∧ IsMultiHomog t a ∧ (∀ k, 0 ≤ γ k + a k) ∧
        IsMultiHomog g (fun k => (γ k + a k).toNat) ∧ z = aeval y g / aeval y t}
  else ⊥

variable [LinearOrder K] [∀ k, LinearOrder (ι k)]

open Classical in

def cellD (y : (Σ k, ι k) → Ω) (n : ℕ) :
    (ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell K ι n → Ω) →ₗ[S] (ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell K ι (n + 1) → Ω) :=
  LinearMap.pi fun I => if CellMeets y I.1 then ∑ k, ∑ i ∈ I.1 k,
    if h : (∀ l, (Function.update I.1 k ((I.1 k).erase i) l).Nonempty) ∧
        ∑ l, ((Function.update I.1 k ((I.1 k).erase i) l).card - 1) = n then
      ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.faceSign I.1 k i •
        LinearMap.proj (R := S) (φ := fun _ : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell K ι n => Ω)
          ⟨Function.update I.1 k ((I.1 k).erase i), h⟩
    else 0
  else 0

def cellC (y : (Σ k, ι k) → Ω) (γ : K → ℤ) (n : ℕ) :
    Submodule S (ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell K ι n → Ω) :=
  Submodule.pi Set.univ fun I => cellSec S y γ I.1

def cellZ (y : (Σ k, ι k) → Ω) (γ : K → ℤ) (n : ℕ) :
    Submodule S (ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell K ι n → Ω) :=
  cellC S y γ n ⊓ LinearMap.ker (cellD S y n)

def cellB (y : (Σ k, ι k) → Ω) (γ : K → ℤ) :
    (n : ℕ) → Submodule S (ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell K ι n → Ω)
  | 0 => ⊥
  | n + 1 => (cellC S y γ n).map (cellD S y n)

abbrev cellH (y : (Σ k, ι k) → Ω) (γ : K → ℤ) (n : ℕ) : Type :=
  ↥(cellZ S y γ n) ⧸ (cellB S y γ n).comap (cellZ S y γ n).subtype

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.CoordIdealXgen
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kleiman

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

def CechExact.Statement : Prop :=
  ∀ (S : Type) [CommRing S] [IsNoetherianRing S] (N : ℕ)
    (M₁ M₂ M₃ : Type) [AddCommGroup M₁] [Module (Poly S N) M₁] [Module S M₁] [IsScalarTower S (Poly S N) M₁]
    [AddCommGroup M₂] [Module (Poly S N) M₂] [Module S M₂] [IsScalarTower S (Poly S N) M₂]
    [AddCommGroup M₃] [Module (Poly S N) M₃] [Module S M₃] [IsScalarTower S (Poly S N) M₃]
    (G₁ : GradedMod S N M₁) (G₂ : GradedMod S N M₂) (G₃ : GradedMod S N M₃)
    (f : M₁ →ₗ[Poly S N] M₂) (g : M₂ →ₗ[Poly S N] M₃)
    (hf : IsGradedHom S N G₁ G₂ f) (hg : IsGradedHom S N G₂ G₃ g),
    Function.Injective f → Function.Exact f g → Function.Surjective g →
    ∀ c : ℤ,
      (∀ i : ℕ,
        (∀ v ∈ cechC (gradedSys S N M₁ G₁ c) i, gradedCmap S N hf c v = 0 → v = 0) ∧
        (∀ v ∈ cechC (gradedSys S N M₂ G₂ c) i, gradedCmap S N hg c v = 0 →
          ∃ u ∈ cechC (gradedSys S N M₁ G₁ c) i, gradedCmap S N hf c u = v) ∧
        (cechC (gradedSys S N M₂ G₂ c) i).map (gradedCmap S N hg c) = cechC (gradedSys S N M₃ G₃ c) i) ∧
      Function.Injective (gradedHmap S N hf 0 c) ∧
      ∃ δ : ∀ i, gradedH S N M₃ G₃ i c →ₗ[S] gradedH S N M₁ G₁ (i + 1) c,
        ∀ i, Function.Exact (gradedHmap S N hf i c) (gradedHmap S N hg i c) ∧
          Function.Exact (gradedHmap S N hg i c) (δ i) ∧
          Function.Exact (δ i) (gradedHmap S N hf (i + 1) c)

def CechTop.Statement : Prop :=
  ∀ (S : Type) [CommRing S] [IsNoetherianRing S] (N : ℕ)
    (M : Type) [AddCommGroup M] [Module (Poly S N) M] [Module S M] [IsScalarTower S (Poly S N) M]
    (G : GradedMod S N M) (i : ℕ), N < i → ∀ c : ℤ, Subsingleton (gradedH S N M G i c)

def CechFlat.Statement : Prop :=
  ∀ (S S' : Type) [CommRing S] [IsNoetherianRing S] [CommRing S'] [Algebra S S'] [Module.Flat S S'] (N : ℕ)
    (M : Type) [AddCommGroup M] [Module (Poly S N) M] [Module S M] [IsScalarTower S (Poly S N) M]
    (G : GradedMod S N M)
    (M' : Type) [AddCommGroup M'] [Module (Poly S' N) M'] [Module S' M'] [IsScalarTower S' (Poly S' N) M']
    [Module S M'] [IsScalarTower S S' M']
    (G' : GradedMod S' N M') (φ : M →ₗ[S] M'),
    IsBaseChange S' φ →
    (∀ (i : Fin (N + 1)) (m : M), φ ((X i : Poly S N) • m) = (X i : Poly S' N) • φ m) →
    (∀ c, ∀ m ∈ G.piece c, φ m ∈ G'.piece c) →
    ∀ (i : ℕ) (c : ℤ), Nonempty (gradedH S' N M' G' i c ≃ₗ[S'] TensorProduct S S' (gradedH S N M G i c))

def Extension.Statement : Prop :=
  ∀ (S : Type) [CommRing S] [IsNoetherianRing S] (N : ℕ) (Ω : Type) [Field Ω] [Algebra S Ω]
    (x : Fin (N + 1) → Ω) (E : Type) [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]
    (F : SubFamily S E x), F.IsFinite →
    ∃ (n : ℕ) (c : Fin n → ℤ) (e : Fin n → E), IsExtensionOf S x F.mods c e

def Generated.Statement : Prop :=
  ∀ (S : Type) [CommRing S] [IsNoetherianRing S] (N : ℕ) (Ω : Type) [Field Ω] [Algebra S Ω]
    (x : Fin (N + 1) → Ω) (Q : LineBundle (S := S) x),
    ∃ c₀ : ℤ, ∀ c : ℤ, c₀ ≤ c → IsGenerated S x (twistA S x Q.mods c)

def GeneratedAmple.Statement : Prop :=
  ∀ (S : Type) [CommRing S] [IsNoetherianRing S] (N : ℕ) (Ω : Type) [Field Ω] [Algebra S Ω]
    (x : Fin (N + 1) → Ω) (H : LineBundle (S := S) x), AmpleData S x H.mods →
    ∀ Q : LineBundle (S := S) x, ∃ c₀ : ℕ, ∀ c : ℕ, c₀ ≤ c → IsGenerated S x (lmul S Q.mods (lpow S H.mods c))

def PrimeFiltration.Statement : Prop :=
  ∀ (S : Type) [CommRing S] [IsNoetherianRing S] (N : ℕ) (Ω : Type) [Field Ω] [Algebra S Ω]
    (x : Fin (N + 1) → Ω),
    (∀ (M : Type) [AddCommGroup M] [Module (Poly S N) M] [Module S M] [IsScalarTower S (Poly S N) M]
      (G : GradedMod S N M), Module.Finite (Poly S N) M → (∀ f ∈ coordIdeal S x, ∀ m : M, f • m = 0) →
      ∃ F : PrimeFiltration S N G,
        (∀ (pp : Ideal (Poly S N)) (hpp : pp ∈ (Module.annihilator (Poly S N) M).minimalPrimes),
          haveI : pp.IsPrime := hpp.1.1
          ((PrimeFiltration.count S N F pp : ℕ) : ℕ∞) =
            Module.length (Localization.AtPrime pp) (LocalizedModule pp.primeCompl M)) ∧
        (∀ k, (∀ i, (X i : Poly S N) ∈ F.prime k) →
          ∃ c₀ : ℤ, ∀ c : ℤ, c₀ ≤ c → ∀ f ∈ polyPiece S N c, f ∈ F.prime k)) ∧
    (∀ (pp : Ideal (Poly S N)) [pp.IsPrime], IsHomogIdeal S pp → coordIdeal S x ≤ pp →
      (∃ j, (X j : Poly S N) ∉ pp) →
      coordIdeal S (ptCoord pp) = pp ∧
      ∀ Q : LineBundle (S := S) x, ∃ QW : Fin (N + 1) → Submodule S (FractionRing (Poly S N ⧸ pp)),
        IsRestrictionOf x pp Q QW ∧
        ∀ (n : ℕ) (c : ℤ), Nonempty (cechH (quotTwistSys S x pp Q.mods c) n ≃ₗ[S]
          famH S (ptCoord pp) (twistA S (ptCoord pp) QW c) n))

def SerrePoly.Statement : Prop :=
  ∀ (S : Type) [CommRing S] [IsNoetherianRing S] (N : ℕ),
    (∀ (i : ℕ) (c : ℤ), Module.Finite S (gradedH S N (Poly S N) (polyGraded S N) i c)) ∧
    ∀ c : ℤ, 0 ≤ c →
      (∀ i : ℕ, 1 ≤ i → Subsingleton (gradedH S N (Poly S N) (polyGraded S N) i c)) ∧
      (∀ m ∈ polyPiece S N c, unitCochain S N (Poly S N) m ∈ gradedZ S N (Poly S N) (polyGraded S N) 0 c) ∧
      (∀ z ∈ gradedZ S N (Poly S N) (polyGraded S N) 0 c,
        ∃! m, m ∈ polyPiece S N c ∧ unitCochain S N (Poly S N) m = z)

def SerreFree.Statement : Prop :=
  ∀ (S : Type) [CommRing S] [IsNoetherianRing S] (N : ℕ)
    (M : Type) [AddCommGroup M] [Module (Poly S N) M] [Module S M] [IsScalarTower S (Poly S N) M]
    (G : GradedMod S N M) (r : ℕ) (d : Fin r → ℤ) (b : Module.Basis (Fin r) (Poly S N) M),
    (∀ j, b j ∈ G.piece (d j)) →
    (∀ (i : ℕ) (c : ℤ), Module.Finite S (gradedH S N M G i c)) ∧
    ∀ c : ℤ, (∀ j, d j ≤ c) →
      (∀ i : ℕ, 1 ≤ i → Subsingleton (gradedH S N M G i c)) ∧
      (∀ m ∈ G.piece c, unitCochain S N M m ∈ gradedZ S N M G 0 c) ∧
      (∀ z ∈ gradedZ S N M G 0 c, ∃! m, m ∈ G.piece c ∧ unitCochain S N M m = z)

def SerreFinite.Statement : Prop :=
  ∀ (S : Type) [CommRing S] [IsNoetherianRing S] (N : ℕ)
    (M : Type) [AddCommGroup M] [Module (Poly S N) M] [Module S M] [IsScalarTower S (Poly S N) M]
    (G : GradedMod S N M), Module.Finite (Poly S N) M →
    ∀ (i : ℕ) (c : ℤ), Module.Finite S (gradedH S N M G i c)

def SerreVanish.Statement : Prop :=
  ∀ (S : Type) [CommRing S] [IsNoetherianRing S] (N : ℕ)
    (M : Type) [AddCommGroup M] [Module (Poly S N) M] [Module S M] [IsScalarTower S (Poly S N) M]
    (G : GradedMod S N M), Module.Finite (Poly S N) M →
    ∃ c₀ : ℤ, ∀ (i : ℕ), 1 ≤ i → ∀ c : ℤ, c₀ ≤ c → Subsingleton (gradedH S N M G i c)

def SerreOnto.Statement : Prop :=
  ∀ (S : Type) [CommRing S] [IsNoetherianRing S] (N : ℕ)
    (M : Type) [AddCommGroup M] [Module (Poly S N) M] [Module S M] [IsScalarTower S (Poly S N) M]
    (G : GradedMod S N M), Module.Finite (Poly S N) M →
    ∃ c₀ : ℤ, ∀ c : ℤ, c₀ ≤ c → ∀ z ∈ gradedZ S N M G 0 c, ∃ m ∈ G.piece c, unitCochain S N M m = z

def SerreTail.Statement : Prop :=
  ∀ (S : Type) [CommRing S] [IsNoetherianRing S] (N : ℕ)
    (M : Type) [AddCommGroup M] [Module (Poly S N) M] [Module S M] [IsScalarTower S (Poly S N) M]
    (G : GradedMod S N M), Module.Finite (Poly S N) M →
    ∀ c₁ : ℤ, ∃ (n : ℕ) (e : Fin n → ℤ) (z : Fin n → ∀ I, LocM S N M I),
      (∀ k, c₁ ≤ e k ∧ z k ∈ gradedZ S N M G 0 (e k)) ∧
      ∀ c : ℤ, c₁ ≤ c → ∀ z' ∈ gradedZ S N M G 0 c,
        z' ∈ ⨆ k, Submodule.span S ((fun f : Poly S N => f • z k) '' (polyPiece S N (c - e k) : Set (Poly S N)))

def TwistFinite.Statement : Prop :=
  ∀ (S : Type) [CommRing S] [IsNoetherianRing S] (N : ℕ) (Ω : Type) [Field Ω] [Algebra S Ω]
    (x : Fin (N + 1) → Ω) (G B : LineBundle (S := S) x) (r : ℕ) (η : Fin (r + 1) → Ω),
    IsGeneratedBy S x B.mods η →
    ∃ (n : ℕ) (bk : Fin n → ℕ) (s : Fin n → Ω),
      (∀ k, s k ∈ secs S x (lmul S G.mods (lpow S B.mods (bk k)))) ∧
      ∀ b : ℕ, secs S x (lmul S G.mods (lpow S B.mods b)) =
        ⨆ k, Submodule.span S (Set.image2 (· * ·) (secZ S η ((b : ℤ) - bk k) : Set Ω) {s k})

def TwistVanish.Statement : Prop :=
  ∀ (S : Type) [CommRing S] [IsNoetherianRing S] (N : ℕ) (Ω : Type) [Field Ω] [Algebra S Ω]
    (x : Fin (N + 1) → Ω) (G B : LineBundle (S := S) x) (r : ℕ) (η : Fin (r + 1) → Ω),
    IsGeneratedBy S x B.mods η →
    ∃ c₀ : ℤ, ∀ (b : ℕ) (c : ℤ), c₀ ≤ c → Subsingleton (famH S x (sumGBA S x G B b c) 1)

section Inhabitants

variable (k : Type) [Field k]

noncomputable def xgen (N : ℕ) : Fin (N + 1) → FractionRing (Poly k N) :=
  fun i => algebraMap (Poly k N) (FractionRing (Poly k N)) (X i)

noncomputable def GeneratedAmple.hyps : AmpleData k (lineX k) (bundleA k (lineX k)).mods := ampleA (lineX k)

noncomputable def PrimeFiltration.example : PrimeFiltration k 1 (polyGraded k 1) := polyFiltration k 1

end Inhabitants

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PAmpleCover
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}

theorem AmpleCover.sub_twist (F Q : SubSystem S x Ω) (I : Chart x) :
    (F.twist Q).sub I = F.sub I * Q.sub I := by
  rw [Submodule.mul_eq_span_mul_set]
  change Submodule.span _ _ = _
  congr 1
  ext z
  simp only [Set.mem_ofPred_eq, Set.mem_mul, SetLike.mem_coe, smul_eq_mul]
  constructor
  · rintro ⟨q, hq, y, hy, rfl⟩; exact ⟨y, hy, q, hq, mul_comm _ _⟩
  · rintro ⟨y, hy, q, hq, rfl⟩; exact ⟨q, hq, y, hy, mul_comm _ _⟩

theorem AmpleCover.sub_pow (Q : SubSystem S x Ω) (n : ℕ) (I : Chart x) :
    (Q.pow n).sub I = Q.sub I ^ n := by
  induction n with
  | zero =>
    obtain ⟨i, hi⟩ := I.2.1
    rw [pow_zero]
    change twistMod S x 0 I = 1
    rw [twistMod_eq_span 0 I hi, zpow_zero, Submodule.one_eq_span]
  | succ n ih =>
    change ((Q.pow n).twist Q).sub I = _
    rw [AmpleCover.sub_twist, ih, pow_succ]

theorem AmpleCover.proof : AmpleCover.Statement.{u, w} := by
  intro S _ Ω _ _ N x H A F hF I
  set R := chartRing S x I
  set G : Submodule R Ω := Submodule.span R (F.secs : Set Ω)
  set P : Submodule R Ω := H.sub I
  refine le_antisymm (Submodule.span_le.mpr fun z hz => ?_) fun y hy => ?_
  · exact (Submodule.mem_iInf _).mp hz I
  obtain ⟨Q', hQ'⟩ := H.invertible I
  have hpow : ∀ n, (H.pow n).sub I = P ^ n := fun n => AmpleCover.sub_pow H.toSubSystem n I
  have hone : ∀ n, P ^ n * Q' ^ n = 1 := fun n => by rw [← mul_pow, hQ', one_pow]

  set c : Ideal R := G.comap (LinearMap.toSpanSingleton R Ω y)
  set V : Submodule R Ω := Submodule.map (Algebra.linearMap R Ω) c.radical
  have hkey : P ^ A.m * Q' ^ A.m ≤ V := by
    rw [← hpow, ← A.generates I, Submodule.mul_le]
    intro u hu w hw
    have hmem : ∀ j, A.h j * w ∈ V := by
      intro j
      have h1 : A.h j * w ∈ (1 : Submodule R Ω) := by
        rw [← hone A.m, ← hpow]
        exact Submodule.mul_mem_mul (by rw [← A.generates I]; exact Submodule.subset_span ⟨j, rfl⟩) hw
      obtain ⟨a, ha⟩ := Submodule.mem_one.mp h1
      obtain ⟨e, he⟩ := hF j I y hy
      refine ⟨a, ⟨e, ?_⟩, ha⟩
      change a ^ e • y ∈ G
      have hw' : w ^ e ∈ Q' ^ (A.m * e) := by
        rw [pow_mul]; exact Submodule.pow_mem_pow _ hw e
      have h2 : (y * A.h j ^ e) * w ^ e ∈ G * P ^ (A.m * e) * Q' ^ (A.m * e) :=
        Submodule.mul_mem_mul (by rw [← hpow]; exact he) hw'
      rw [mul_assoc, hone, mul_one] at h2
      rw [Algebra.smul_def, map_pow]
      change ((a : Ω)) ^ e * y ∈ G
      have : (a : Ω) = A.h j * w := ha
      rw [this]
      convert h2 using 1
      ring
    refine Submodule.span_induction (p := fun u _ => u * w ∈ V) ?_ ?_ ?_ ?_ hu
    · rintro _ ⟨j, rfl⟩; exact hmem j
    · rw [zero_mul]; exact V.zero_mem
    · intro a b _ _ ha hb; rw [add_mul]; exact V.add_mem ha hb
    · intro r a _ ha; rw [smul_mul_assoc]; exact V.smul_mem r ha
  obtain ⟨b, ⟨n, hn⟩, hb⟩ := hkey (by rw [hone]; exact Submodule.mem_one.mpr ⟨1, map_one _⟩)
  have hb1 : (b : Ω) = 1 := hb
  have hbn : b ^ n • y ∈ G := hn
  rwa [Algebra.smul_def, map_pow, show algebraMap R Ω b = 1 from hb1, one_pow, one_mul] at hbn

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PAmpleTwistLocal
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

namespace AmpleTwistLocal

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}

theorem mem_chartRing_of_mem_zero {I : Chart x} {q : Ω} (hq : q ∈ twistMod S x 0 I) :
    q ∈ chartRing S x I := by
  refine Submodule.span_induction (p := fun q _ => q ∈ chartRing S x I) ?_ ?_ ?_ ?_ hq
  · rintro _ ⟨f, s, e, e', hs, hf, hse, he, rfl⟩
    have hee : e' = e := by omega
    subst hee
    exact ⟨f, s, e', hs, hf, hse, rfl⟩
  · exact Subalgebra.zero_mem _
  · intro a b _ _ ha hb; exact Subalgebra.add_mem _ ha hb
  · intro a q _ hq
    rw [chartRing_smul_def]
    exact Subalgebra.mul_mem _ a.2 hq

theorem mul_mem_pow (H : SubSystem S x Ω) (I : Chart x) {c : ℕ} {z : Ω}
    (hz : z ∈ (H.pow c).sub I) (d : ℕ) {w : Ω} (hw : w ∈ (H.pow d).sub I) :
    z * w ∈ (H.pow (c + d)).sub I := by
  induction d generalizing w with
  | zero =>
    change w ∈ twistMod S x 0 I at hw
    have h := Submodule.smul_mem ((H.pow c).sub I)
      (⟨w, mem_chartRing_of_mem_zero hw⟩ : chartRing S x I) hz
    rw [chartRing_smul_def] at h
    rwa [Nat.add_zero, mul_comm]
  | succ d ih =>
    change w ∈ Submodule.span _ _ at hw
    refine Submodule.span_induction
      (p := fun w _ => z * w ∈ ((H.pow (c + d)).twist H).sub I) ?_ ?_ ?_ ?_ hw
    · rintro _ ⟨q, hq, y, hy, rfl⟩
      refine Submodule.subset_span ⟨q, hq, z * y, ih hy, ?_⟩
      simp only [smul_eq_mul]; ring
    · rw [mul_zero]; exact Submodule.zero_mem _
    · intro a b _ _ ha hb; rw [mul_add]; exact Submodule.add_mem _ ha hb
    · intro a w _ hw
      rw [chartRing_smul_def, mul_left_comm, ← chartRing_smul_def]
      exact Submodule.smul_mem _ a hw

theorem pow_mem_pow (H : SubSystem S x Ω) (I : Chart x) {m : ℕ} {h : Ω}
    (hh : h ∈ (H.pow m).sub I) (n : ℕ) : h ^ n ∈ (H.pow (m * n)).sub I := by
  induction n with
  | zero =>
    rw [pow_zero]
    exact one_mem_twistMod_zero I
  | succ n ih =>
    rw [pow_succ, Nat.mul_succ]
    exact mul_mem_pow H I ih m hh

theorem mul_mem_twist_pow (Q H : SubSystem S x Ω) (I : Chart x) {c d : ℕ} {z w : Ω}
    (hz : z ∈ (Q.twist (H.pow c)).sub I) (hw : w ∈ (H.pow d).sub I) :
    z * w ∈ (Q.twist (H.pow (c + d))).sub I := by
  change z ∈ Submodule.span _ _ at hz
  refine Submodule.span_induction
    (p := fun z _ => z * w ∈ (Q.twist (H.pow (c + d))).sub I) ?_ ?_ ?_ ?_ hz
  · rintro _ ⟨q, hq, y, hy, rfl⟩
    refine Submodule.subset_span ⟨q * w, mul_mem_pow H I hq d hw, y, hy, ?_⟩
    simp only [smul_eq_mul]; ring
  · rw [zero_mul]; exact Submodule.zero_mem _
  · intro a b _ _ ha hb; rw [add_mul]; exact Submodule.add_mem _ ha hb
  · intro a z _ hz
    rw [chartRing_smul_def, mul_assoc, ← chartRing_smul_def]
    exact Submodule.smul_mem _ a hz

theorem proof (hA : AmpleAffineGen.Statement.{u, w}) : AmpleTwistLocal.Statement.{u, w} := by
  intro S _ _ Ω _ _ N x H A Q b j
  classical
  by_cases h0 : A.h j = 0
  · refine ⟨0, fun n _ I y _ => ⟨1, ?_⟩⟩
    rw [h0, pow_one, mul_zero]
    exact Submodule.zero_mem _
  obtain ⟨p, s, hs, hgen⟩ := hA S Ω N x H A Q b j h0
  have hhI : ∀ I : Chart x, A.h j ∈ (H.pow A.m).sub I := fun I =>
    (Submodule.mem_iInf _).mp (A.mem_secs j) I
  choose k hk using hs
  refine ⟨Finset.univ.sup fun q : Fin p × Chart x => k q.1 q.2, fun n hn I y hy => ?_⟩
  have hglob : ∀ t, s t * A.h j ^ n ∈ (Q.twist (H.pow (b + A.m * n))).secs := by
    intro t
    refine (Submodule.mem_iInf _).mpr fun I' => ?_
    have hle : k t I' ≤ n := le_trans
      (Finset.le_sup (f := fun q : Fin p × Chart x => k q.1 q.2) (Finset.mem_univ (t, I'))) hn
    have h1 := mul_mem_twist_pow Q.toSubSystem H.toSubSystem I' (hk t I')
      (pow_mem_pow H.toSubSystem I' (hhI I') (n - k t I'))
    have e1 : s t * A.h j ^ k t I' * A.h j ^ (n - k t I') = s t * A.h j ^ n := by
      rw [mul_assoc, ← pow_add, Nat.add_sub_cancel' hle]
    have e2 : b + A.m * k t I' + A.m * (n - k t I') = b + A.m * n := by
      rw [add_assoc, ← mul_add, Nat.add_sub_cancel' hle]
    rw [e1, e2] at h1
    exact h1
  have hpn : A.h j ^ n ≠ 0 := pow_ne_zero n h0
  obtain ⟨e, g, hg, hz⟩ := hgen I (y / A.h j ^ n) n (by rwa [div_mul_cancel₀ y hpn])
  refine ⟨e, ?_⟩
  have hy' : y = A.h j ^ n * ∑ t, g t * s t := by
    rw [← hz]; field_simp
  rw [hy', Finset.mul_sum, Finset.sum_mul]
  refine Submodule.sum_mem _ fun t _ => ?_
  have e3 : A.h j ^ n * (g t * s t) * A.h j ^ e = (s t * A.h j ^ n) * (g t * A.h j ^ e) := by ring
  rw [e3]
  exact Submodule.mul_mem_mul (Submodule.subset_span (hglob t)) (hg t)

end AmpleTwistLocal

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PCechTop
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

theorem CechTop.idx_isEmpty (N i : ℕ) (hi : N < i) :
    IsEmpty (Cech.Idx (Finset.univ : Finset (Fin (N + 1))) i) := by
  refine ⟨fun I => ?_⟩
  have h1 : I.1.1.card ≤ N + 1 := by
    simpa using Finset.card_le_univ I.1.1
  have h2 := I.2
  omega

theorem CechTop.proof : CechTop.Statement := by
  intro S _ _ N M _ _ _ _ 𝓜 i c hi
  have := CechTop.idx_isEmpty N i hi
  have hC : Subsingleton (Cech.Cochain (locSys S N M) i) := inferInstance
  constructor
  intro a b
  change (a : Cech.Hdeg _ _ _ i) = b
  induction a using Submodule.Quotient.induction_on with
  | H x =>
    induction b using Submodule.Quotient.induction_on with
    | H y =>
      congr 1
      exact Subtype.ext (hC.elim _ _)

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PGeneratedAmple
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

noncomputable section

universe u w

theorem GeneratedAmple.proof (hCover : AmpleCover.Statement.{u, w})
    (hLocal : AmpleTwistLocal.Statement.{u, w}) : GeneratedAmple.Statement.{u, w} := by
  intro S _ _ Ω _ _ N x H A Q
  choose n₀ hn₀ using fun (b : Fin A.m) (j : Fin (A.r + 1)) => hLocal S Ω N x H A Q b j
  let M : ℕ := Finset.univ.sup fun p : Fin A.m × Fin (A.r + 1) => n₀ p.1 p.2
  refine ⟨A.m * M, fun c hc => hCover S Ω N x H A _ fun j I y hy => ?_⟩
  have hm := A.m_pos
  have hc' : c % A.m + A.m * (c / A.m) = c := Nat.mod_add_div c A.m
  have hM : M ≤ c / A.m := (Nat.le_div_iff_mul_le hm).mpr (by rw [mul_comm]; exact hc)
  have hn : n₀ ⟨c % A.m, Nat.mod_lt c hm⟩ j ≤ c / A.m :=
    le_trans (Finset.le_sup (f := fun p : Fin A.m × Fin (A.r + 1) => n₀ p.1 p.2)
      (Finset.mem_univ (⟨c % A.m, Nat.mod_lt c hm⟩, j))) hM
  have key := hn₀ ⟨c % A.m, Nat.mod_lt c hm⟩ j (c / A.m) hn I y
  simp only [hc'] at key
  exact key hy

end

end GroundTheory.Heights₂.Heights.Kleiman
end

