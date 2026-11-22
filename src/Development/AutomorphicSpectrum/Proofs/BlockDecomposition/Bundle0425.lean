import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsOpenFixedOfSubgroup
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0413
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle0055
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle0052
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNormalised
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0410
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0304
import Development.WeilBound.CoreStatements.EulerCharacteristicCounts.Bundle0002
import GroundTheory.ProfiniteCohomology.LocalClassFormation.CupSymbol
import GroundTheory.ProfiniteCohomology.GaloisCohomology.IsZeroGroupCohomologyQuotientToInvariantsGalAdd
import GroundTheory.ProfiniteCohomology.GaloisCohomology.Kummer
import GroundTheory.GlobalFields.LocalFieldAtPlace
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.TransportA
import GroundTheory.GlobalFields.KummerTheory.LocalIndexAtPlace
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0414
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.StrictDominanceCasselman.IsStrictlyDominant

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoFunSmooth
section
open GlobalTheory.PRep GlobalTheory.SmGL

noncomputable section

namespace GlobalTheory.CompanionTheory.CIndCoinv

section Abstract

variable {G M W W' : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group M]
  [TopologicalSpace M] [IsTopologicalGroup M] [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']

def coFun (s : M →* G) (χ : M →* ℂˣ) (c : W →ₗ[ℂ] W') (f : G → W) (x : M) : W' :=
  (χ x : ℂ) • c (f (s x))

theorem coFun_mem {H : Subgroup G} {Q : Subgroup M} (s : M →* G) (hQH : ∀ p ∈ Q, s p ∈ H) (χ : M →* ℂˣ)
    (σ : Representation ℂ H W) (σ' : Representation ℂ Q W') (c : W →ₗ[ℂ] W')
    (hcomp : ∀ (p : Q) (w : W), (χ p : ℂ) • c (σ ⟨s p, hQH p p.2⟩ w) = σ' p (c w)) (f : indSpace H σ) :
    coFun s χ c f.1 ∈ indSpace Q σ' := by
  intro p x
  have h1 : f.1 (s p * s x) = σ ⟨s p, hQH p p.2⟩ (f.1 (s x)) := f.2 ⟨s p, hQH p p.2⟩ (s x)
  show ((χ ((p : M) * x) : ℂˣ) : ℂ) • c (f.1 (s ((p : M) * x))) = σ' p (((χ x : ℂˣ) : ℂ) • c (f.1 (s x)))
  rw [map_mul, map_mul, h1, map_smul, ← hcomp, Units.val_mul, mul_comm, mul_smul]

theorem coFun_smooth {H : Subgroup G} {Q : Subgroup M} (s : M →* G) (hs : Continuous s) (hQH : ∀ p ∈ Q, s p ∈ H)
    (χ : M →* ℂˣ) (hχ : IsOpen (χ.ker : Set M))
    (σ : Representation ℂ H W) (σ' : Representation ℂ Q W') (c : W →ₗ[ℂ] W')
    (hcomp : ∀ (p : Q) (w : W), (χ p : ℂ) • c (σ ⟨s p, hQH p p.2⟩ w) = σ' p (c w)) (f : smoothPart (ind H σ)) :
    (⟨coFun s χ c f.1.1, coFun_mem s hQH χ σ σ' c hcomp f.1⟩ : indSpace Q σ') ∈ smoothPart (ind Q σ') := by
  refine mem_smoothPart_of_nhds (Filter.mem_of_superset
    (((IsOpen.preimage hs f.2).inter hχ).mem_nhds ?_) ?_)
  · refine ⟨?_, one_mem _⟩
    simp
  · rintro x ⟨h1, h2⟩
    have h1' : ind H σ (s x) f.1 = f.1 := h1
    have h2' : χ x = 1 := h2
    apply Subtype.ext
    funext y
    show ((χ (y * x) : ℂˣ) : ℂ) • c (f.1.1 (s (y * x))) = ((χ y : ℂˣ) : ℂ) • c (f.1.1 (s y))
    have h3 : f.1.1 (s y * s x) = f.1.1 (s y) := congrFun (congrArg Subtype.val h1') (s y)
    rw [map_mul, map_mul, h2', mul_one, h3]

end Abstract

section Abstract2

variable {G M W W' : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group M]
  [TopologicalSpace M] [IsTopologicalGroup M] [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']

def coMap {H : Subgroup G} {Q : Subgroup M} (s : M →* G) (hs : Continuous s) (hQH : ∀ p ∈ Q, s p ∈ H)
    (χ : M →* ℂˣ) (hχ : IsOpen (χ.ker : Set M))
    (σ : Representation ℂ H W) (σ' : Representation ℂ Q W') (c : W →ₗ[ℂ] W')
    (hcomp : ∀ (p : Q) (w : W), (χ p : ℂ) • c (σ ⟨s p, hQH p p.2⟩ w) = σ' p (c w)) :
    cIndSpace H σ →ₗ[ℂ] smoothPart (ind Q σ') where
  toFun f := ⟨⟨coFun s χ c f.1.1.1, coFun_mem s hQH χ σ σ' c hcomp f.1.1⟩, coFun_smooth s hs hQH χ hχ σ σ' c hcomp f.1⟩
  map_add' a b := by
    apply Subtype.ext
    apply Subtype.ext
    funext x
    show ((χ x : ℂˣ) : ℂ) • c (a.1.1.1 (s x) + b.1.1.1 (s x)) = _
    rw [map_add, smul_add]
    rfl
  map_smul' r a := by
    apply Subtype.ext
    apply Subtype.ext
    funext x
    show ((χ x : ℂˣ) : ℂ) • c (r • a.1.1.1 (s x)) = r • (((χ x : ℂˣ) : ℂ) • c (a.1.1.1 (s x)))
    rw [map_smul, smul_comm]

theorem coinv_equiv (H U : Subgroup G) (Q : Subgroup M) (s : M →* G) (q : G →* M)
    (hH : IsClosed (H : Set G))
    (hbasis : ∀ O : Set G, O ∈ nhds (1 : G) → ∃ K : Subgroup G, IsOpen (K : Set G) ∧ IsCompact (K : Set G) ∧ (K : Set G) ⊆ O)
    (hs : Continuous s) (hq : Continuous q) (hqs : ∀ x, q (s x) = x) (hker : ∀ g, q g = 1 ↔ g ∈ U)
    (hUH : U ≤ H) (hHQ : ∀ g ∈ H, q g ∈ Q) (hQH : ∀ p ∈ Q, s p ∈ H)
    (C : Set M) (hC : IsCompact C) (hMC : ∀ x : M, ∃ p ∈ Q, ∃ y ∈ C, x = p * y)
    (χ : M →* ℂˣ) (hχ : IsOpen (χ.ker : Set M))
    (σ : Representation ℂ H W) (hσ : IsSmooth σ) (σ' : Representation ℂ Q W')
    (c : W →ₗ[ℂ] W') (hc : Function.Surjective c) (hck : ∀ w, c w = 0 ↔ w ∈ twKer σ (U.subgroupOf H) 1)
    (hcomp : ∀ (p : Q) (w : W), (χ p : ℂ) • c (σ ⟨s p, hQH p p.2⟩ w) = σ' p (c w))
    (hK : ∀ f : cIndSpace H σ, (∀ g, f.1.1.1 g ∈ twKer σ (U.subgroupOf H) 1) → f ∈ twKer (cInd H σ) U 1) :
    ∃ E : (cIndSpace H σ ⧸ twKer (cInd H σ) U 1) ≃ₗ[ℂ] smoothPart (ind Q σ'),
      ∀ (f : cIndSpace H σ) (x : M), (E (Submodule.Quotient.mk f)).1.1 x = (χ x : ℂ) • c (f.1.1.1 (s x)) := by
  classical
  haveI hUn : U.Normal := by
    have : U = q.ker := by
      ext g
      rw [MonoidHom.mem_ker, hker]
    rw [this]
    infer_instance
  have hcu : ∀ (u : G) (hu : u ∈ U) (w : W), c (σ ⟨u, hUH hu⟩ w) = c w := by
    intro u hu w
    have : σ ⟨u, hUH hu⟩ w - w ∈ twKer σ (U.subgroupOf H) 1 :=
      Submodule.subset_span ⟨⟨⟨u, hUH hu⟩, hu⟩, w, by simp⟩
    have h2 := (hck _).2 this
    rwa [map_sub, sub_eq_zero] at h2
  have hdec : ∀ g : G, g * (s (q g))⁻¹ ∈ U := by
    intro g
    rw [← hker, map_mul, map_inv, hqs, mul_inv_cancel]
  set Φ := coMap s hs hQH χ hχ σ σ' c hcomp with hΦ
  have hkill : twKer (cInd H σ) U 1 ≤ LinearMap.ker Φ := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨u, f, rfl⟩
    show Φ _ = 0
    apply Subtype.ext
    apply Subtype.ext
    funext x
    have hn : s x * u * (s x)⁻¹ ∈ U := hUn.conj_mem _ u.2 _
    have e : (cInd H σ (u : G) f).1.1.1 (s x) = σ ⟨_, hUH hn⟩ (f.1.1.1 (s x)) := by
      have := f.1.1.2 ⟨_, hUH hn⟩ (s x)
      rw [← this]
      show f.1.1.1 (s x * u) = f.1.1.1 (s x * u * (s x)⁻¹ * s x)
      congr 1
      group
    show ((χ x : ℂˣ) : ℂ) • c ((cInd H σ (u : G) f - ((1 : U →* ℂˣ) u : ℂ) • f).1.1.1 (s x)) = 0
    have e2 : (cInd H σ (u : G) f - ((1 : U →* ℂˣ) u : ℂ) • f).1.1.1 (s x)
        = (cInd H σ (u : G) f).1.1.1 (s x) - f.1.1.1 (s x) := by
      simp
    rw [e2, e, map_sub, hcu _ hn, sub_self, smul_zero]
  have hinj : ∀ f : cIndSpace H σ, Φ f = 0 → f ∈ twKer (cInd H σ) U 1 := by
    intro f hf
    refine hK f fun g => ?_
    rw [← hck]
    have h1 : ∀ x, c (f.1.1.1 (s x)) = 0 := by
      intro x
      have h2 : ((χ x : ℂˣ) : ℂ) • c (f.1.1.1 (s x)) = 0 := by
        have := congrArg (fun F : smoothPart (ind Q σ') => F.1.1 x) hf
        exact this
      exact (smul_eq_zero.1 h2).resolve_left (Units.ne_zero _)
    have h3 : f.1.1.1 g = σ ⟨_, hUH (hdec g)⟩ (f.1.1.1 (s (q g))) := by
      rw [← f.1.1.2 ⟨_, hUH (hdec g)⟩ (s (q g))]
      congr 1
      group
    rw [h3, hcu _ (hdec g), h1]
  have hmemH : ∀ g, q g ∈ Q → g ∈ H := by
    intro g hg
    have : g = (g * (s (q g))⁻¹) * s (q g) := by group
    rw [this]
    exact mul_mem (hUH (hdec g)) (hQH _ hg)
  let qH : H →* Q := (q.comp H.subtype).codRestrict Q fun h => hHQ h h.2
  let σb : Representation ℂ H W' := twist (σ'.comp qH) (χ.comp (q.comp H.subtype))⁻¹
  have hσb : ∀ (h : H) (w : W'), σb h w = (((χ (q h))⁻¹ : ℂˣ) : ℂ) • σ' (qH h) w := fun h w => rfl
  have hcb : ∀ (h : H) (w : W), c (σ h w) = σb h (c w) := by
    intro h w
    have hp : q h ∈ Q := hHQ h h.2
    have e : h = ⟨_, hUH (hdec h)⟩ * ⟨s (q h), hQH _ hp⟩ := by
      apply Subtype.ext
      show (h : G) = (h : G) * (s (q h))⁻¹ * s (q h)
      group
    have e1 : c (σ h w) = c (σ ⟨s (q h), hQH _ hp⟩ w) := by
      conv_lhs => rw [e, map_mul, Module.End.mul_apply]
      rw [hcu _ (hdec h)]
    rw [e1, hσb]
    have := hcomp ⟨q h, hp⟩ w
    show _ = (((χ (q h))⁻¹ : ℂˣ) : ℂ) • σ' ⟨q h, hp⟩ (c w)
    rw [← this, smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]
  have hsurj : ∀ φ : smoothPart (ind Q σ'), ∃ f, Φ f = φ := by
    intro φ
    let b : G → W' := fun g => (((χ (q g))⁻¹ : ℂˣ) : ℂ) • φ.1.1 (q g)
    have hb : b ∈ indSpace H σb := by
      intro h g
      have h1 : φ.1.1 (q h * q g) = σ' (qH h) (φ.1.1 (q g)) := φ.1.2 (qH h) (q g)
      show (((χ (q ((h : G) * g)))⁻¹ : ℂˣ) : ℂ) • φ.1.1 (q ((h : G) * g)) = σb h ((((χ (q g))⁻¹ : ℂˣ) : ℂ) • φ.1.1 (q g))
      rw [map_mul, h1, map_smul, hσb, map_mul, mul_inv, Units.val_mul, smul_smul, mul_comm]
    have hbs : (⟨b, hb⟩ : indSpace H σb) ∈ smoothPart (ind H σb) := by
      refine mem_smoothPart_of_nhds (Filter.mem_of_superset
        (((IsOpen.preimage hq φ.2).inter (IsOpen.preimage hq hχ)).mem_nhds ?_) ?_)
      · refine ⟨?_, ?_⟩
        · simp
        · simp
      · rintro x ⟨h1, h2⟩
        have h1' : ind Q σ' (q x) φ.1 = φ.1 := h1
        have h2' : χ (q x) = 1 := h2
        apply Subtype.ext
        funext y
        show (((χ (q (y * x)))⁻¹ : ℂˣ) : ℂ) • φ.1.1 (q (y * x)) = (((χ (q y))⁻¹ : ℂˣ) : ℂ) • φ.1.1 (q y)
        have h3 : φ.1.1 (q y * q x) = φ.1.1 (q y) := congrFun (congrArg Subtype.val h1') (q y)
        rw [map_mul, map_mul, h2', mul_one, h3]
    have hbc : (⟨⟨b, hb⟩, hbs⟩ : smoothPart (ind H σb)) ∈ cIndSpace H σb := by
      refine ⟨s '' C, hC.image hs, fun g _ => ?_⟩
      obtain ⟨p, hp, y, hy, e⟩ := hMC (q g)
      refine ⟨g * (s y)⁻¹, hmemH _ ?_, s y, ⟨y, hy, rfl⟩, by group⟩
      rw [map_mul, map_inv, hqs, e]
      simpa using hp
    obtain ⟨F, hF⟩ := GlobalTheory.CompanionTheory.BZMirOnto.cInd_lift H hH hbasis σ σb c hc hcb (fun w _ => by
      let S : Subgroup H :=
        { carrier := {h | σ h w = w}
          one_mem' := by simp
          mul_mem' := fun {a b} ha hb => by
            simp only [Set.mem_setOf_eq, map_mul, Module.End.mul_apply] at *
            rw [hb, ha]
          inv_mem' := fun {a} ha => by
            simp only [Set.mem_setOf_eq] at *
            conv_lhs => rw [← ha]
            rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }
      exact ⟨S, hσ w, fun t ht _ => ht⟩) ⟨⟨⟨b, hb⟩, hbs⟩, hbc⟩
    refine ⟨F, Subtype.ext (Subtype.ext (funext fun x => ?_))⟩
    show ((χ x : ℂˣ) : ℂ) • c (F.1.1.1 (s x)) = φ.1.1 x
    rw [hF]
    show ((χ x : ℂˣ) : ℂ) • ((((χ (q (s x)))⁻¹ : ℂˣ) : ℂ) • φ.1.1 (q (s x))) = φ.1.1 x
    rw [hqs, smul_smul, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_smul]
  let L := (twKer (cInd H σ) U 1).liftQ Φ hkill
  have hL : Function.Bijective L := by
    constructor
    · rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
      intro x hx
      obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      exact (Submodule.Quotient.mk_eq_zero _).2 (hinj f hx)
    · intro φ
      obtain ⟨f, hf⟩ := hsurj φ
      exact ⟨Submodule.Quotient.mk f, hf⟩
  exact ⟨LinearEquiv.ofBijective L hL, fun f x => rfl⟩

end Abstract2

end GlobalTheory.CompanionTheory.CIndCoinv
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CommuteLeviBoundaryAndLift
section
noncomputable section

open Finset

namespace GlobalTheory.CompanionTheory.PairMult.CapProdProof

open Formalism.REAL (GlRel qdet)
open CompanionTheory.D.LK (Pos)
open GlobalTheory.CompanionTheory.RgCOBlock (fa fb sz)

variable {n : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W]

theorem evalPair_injLeft_eq_eval (E1 E2 : Fin n → Fin n → Module.End ℂ W) (s : Bool) (z : FreeAlgebra ℂ (Fin n × Fin n)) :
    ev2 E1 E2 (injL s z) = CompanionTheory.D.LK.ev (if s then E1 else E2) z := by
  have e : (ev2 E1 E2).comp (injL s) = CompanionTheory.D.LK.ev (if s then E1 else E2) := by
    apply FreeAlgebra.hom_ext
    funext p
    cases s <;> simp [ev2, injL, CompanionTheory.D.LK.ev]
  exact DFunLike.congr_fun e z

theorem evB_injL (lev : Fin n → ℕ) (X1 X2 : Fin n → Fin n → Module.End ℂ W) (s : Bool)
    (z : FreeAlgebra ℂ (Fin n × Fin n)) :
    evB lev X1 X2 (injL s z) = CompanionTheory.RgExh.U.evL lev (if s then X1 else X2) z := by
  have e : (evB lev X1 X2).comp (injL s) = CompanionTheory.RgExh.U.evL lev (if s then X1 else X2) := by
    apply FreeAlgebra.hom_ext
    funext p
    cases s <;> simp [evB, injL, CompanionTheory.RgExh.U.evL]
  exact DFunLike.congr_fun e z

theorem commute_ev (T : Module.End ℂ W) (E : Fin n → Fin n → Module.End ℂ W) (h : ∀ p q, Commute T (E p q))
    (z : FreeAlgebra ℂ (Fin n × Fin n)) : Commute T (CompanionTheory.D.LK.ev E z) := by
  induction z using FreeAlgebra.induction with
  | grade0 r => rw [AlgHom.commutes]; exact (Algebra.commutes r T).symm
  | grade1 p => simpa [CompanionTheory.D.LK.ev] using h p.1 p.2
  | mul a b ha hb => rw [map_mul]; exact ha.mul_right hb
  | add a b ha hb => rw [map_add]; exact ha.add_right hb

def wL {V : Type} [AddCommGroup V] [Module ℂ V] (s : Bool) (w : Pos n → V) (l : Lt n) : V :=
  (1 / 2 : ℂ) • (if l.1 || s then w l.2 else -w l.2)

theorem sum_letters (lev : Fin n → ℕ) (E1 E2 : Fin n → Fin n → Module.End ℂ W) (s : Bool) (w : Pos n → W) :
    (∑ l : Lt n, if inUL lev l then Tl E1 E2 l (wL s w l) else 0) =
      ∑ i : Pos n, if CompanionTheory.RgExh.U.inU lev i then (if s then E1 else E2) i.1.1 i.1.2 (w i) else 0 := by
  rw [Fintype.sum_prod_type, Fintype.sum_bool, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hi : lev i.1.1 < lev i.1.2
  · cases s <;> simp [hi, Tl, Ts, wL, CompanionTheory.RgExh.U.inU] <;> module
  · simp [hi, CompanionTheory.RgExh.U.inU]

theorem isSubL_inUL (lev : Fin n → ℕ) : IsSubL lev (inUL lev) := by
  refine ⟨fun l h => h, fun s t i j k h1 h2 h3 hi hj => ?_⟩
  show lev k.1.1 < lev k.1.2
  have a : lev i.1.1 < lev i.1.2 := hi
  have b : lev j.1.1 < lev j.1.2 := hj
  rw [h2, h3]
  rw [h1] at a
  exact a.trans b

theorem commute_levi_boundary_and_lift (n M : ℕ) (lev : Fin n → ℕ) (h : ∑ i, sz lev M i = n) (hm : Monotone lev)
    (hlev : ∀ (i : Fin M) (p : Fin (sz lev M i)), lev (GlobalTheory.SmGL.stdBlocks (sz lev M) h ⟨i, p⟩) = (i : ℕ))
    (s : Bool) (Y : ℂ) (V : Type) [AddCommGroup V] [Module ℂ V] (E1 E2 : Fin n → Fin n → Module.End ℂ V)
    (hP : PairRel E1 E2) :
    (∀ l, inUL lev l → Commute (Tl E1 E2 l) (ev2 E1 E2 (injL s (fa n Y)))) ∧
      ∀ x : V, ∃ w : Lt n → V, ev2 E1 E2 (injL s (fa n Y)) x - evB lev E1 E2 (injL s (fb (sz lev M) h Y)) x =
        ∑ l : Lt n, if inUL lev l then Tl E1 E2 l (w l) else 0 := by
  have hG : GlRel (if s then E1 else E2) := by
    cases s
    · simpa using hP.2.1
    · simpa using hP.1
  obtain ⟨c1, c2⟩ := GlobalTheory.CompanionTheory.RgCOBlock.co_hyp n M lev (sz lev M) h Y hm hlev V _ hG
  refine ⟨fun l hl => ?_, fun x => ?_⟩
  · rw [evalPair_injLeft_eq_eval]
    have hc := c1 l.2 hl
    have h1 : Commute (E1 l.2.1.1 l.2.1.2) (CompanionTheory.D.LK.ev (if s then E1 else E2) (fa n Y)) := by
      cases s
      · exact commute_ev _ _ (fun p q => hP.2.2 _ _ p q) _
      · simpa using hc
    have h2 : Commute (E2 l.2.1.1 l.2.1.2) (CompanionTheory.D.LK.ev (if s then E1 else E2) (fa n Y)) := by
      cases s
      · simpa using hc
      · exact commute_ev _ _ (fun p q => (hP.2.2 p q _ _).symm) _
    rcases l with ⟨b, i⟩
    cases b
    · simpa [Tl, Ts] using h1.sub_left h2
    · simpa [Tl, Ts] using h1.add_left h2
  · obtain ⟨w, hw⟩ := c2 x
    refine ⟨wL s w, ?_⟩
    rw [sum_letters, evalPair_injLeft_eq_eval, evB_injL]
    exact hw

theorem capProd : GenCOU2 → CapProd := by
  intro hG n M lev h hm hM V _ _ E1 E2 hP s Y r hq j x hS hD hc
  have hlev := (GlobalTheory.CompanionTheory.RgCOBlock.stdBlocks_clusters n M lev h hm hM).1
  obtain ⟨w, w1, w2, w3⟩ := hG n lev (inUL lev) (injL s (fa n Y)) (injL s (fb (sz lev M) h Y)) hm (isSubL_inUL lev)
    (fun V _ _ E1 E2 hP => commute_levi_boundary_and_lift n M lev h hm hlev s Y V E1 E2 hP) V E1 E2 hP j x hS hD hc
  refine ⟨w, w1, w2, ?_⟩
  rw [← w3, evalPair_injLeft_eq_eval, GlobalTheory.CompanionTheory.RgCOBlock.ev_fa, hq]
  congr 1

end GlobalTheory.CompanionTheory.PairMult.CapProdProof
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstEqOne
section
noncomputable section

open GlobalTheory.SmGL ValuativeRel

namespace GlobalTheory.CompanionTheory.ExtCharU

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem pw_add {n : ℕ} (ξ : Fin n → ℂˣ) (x y : Fin n → ℤ) :
    GlobalTheory.BCT.pw ξ (x + y) = GlobalTheory.BCT.pw ξ x * GlobalTheory.BCT.pw ξ y := by
  simp only [GlobalTheory.BCT.pw, Pi.add_apply, zpow_add, Units.val_mul, Finset.prod_mul_distrib]

theorem pw_ne_zero {n : ℕ} (ξ : Fin n → ℂˣ) (x : Fin n → ℤ) : GlobalTheory.BCT.pw ξ x ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun i _ => Units.ne_zero _

def dg {n : ℕ} (ϖ : kˣ) (e : Fin n → ℤ) : Fin n → kˣ := fun i => ϖ ^ e i

theorem dg_add {n : ℕ} (ϖ : kˣ) (x y : Fin n → ℤ) : dg ϖ (x + y) = dg ϖ x * dg ϖ y := by
  funext i; simp [dg, zpow_add]

theorem ord_zpow (ϖ : kˣ) (m : ℤ) : ord k (ϖ ^ m) = m * ord k ϖ := by
  let o : kˣ →* Multiplicative ℤ := MonoidHom.mk' (fun x => .ofAdd (ord k x)) fun x y => by
    rw [ord_mul, ofAdd_add]
  have h := map_zpow o ϖ m
  have h2 : ord k (ϖ ^ m) = m • ord k ϖ := by
    have := congrArg Multiplicative.toAdd h
    simpa [o] using this
  simpa using h2

def rr (n : ℕ) : Fin n → ℤ := fun i => (n : ℤ) - 1 - (i : ℕ)

theorem rr_anti (n : ℕ) : StrictAnti (rr n) := fun i j h => by
  have : (i : ℕ) < j := h
  simp only [rr]; omega

theorem rr_smul_anti (n : ℕ) {N : ℤ} (hN : 0 < N) : StrictAnti (N • rr n) := fun i j h => by
  have := rr_anti n h
  simp only [Pi.smul_apply, smul_eq_mul]
  exact mul_lt_mul_of_pos_left this hN

theorem add_anti {n : ℕ} (e : Fin n → ℤ) :
    ∃ N : ℤ, 0 < N ∧ StrictAnti (e + N • rr n) := by
  refine ⟨1 + 2 * ∑ i, |e i|, by positivity, fun i j h => ?_⟩
  have hij : (i : ℕ) < j := h
  have hi : |e i| ≤ ∑ l, |e l| :=
    Finset.single_le_sum (f := fun l => |e l|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i)
  have hj : |e j| ≤ ∑ l, |e l| :=
    Finset.single_le_sum (f := fun l => |e l|) (fun _ _ => abs_nonneg _) (Finset.mem_univ j)
  have h1 := abs_le.1 (le_refl |e i|)
  have h2 := abs_le.1 (le_refl |e j|)
  set S := ∑ l, |e l|
  have hd : (1 : ℤ) ≤ rr n i - rr n j := by simp only [rr]; omega
  have hS : 0 ≤ S := Finset.sum_nonneg fun _ _ => abs_nonneg _
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  nlinarith

variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]

theorem const_eq_one (R : Representation ℂ (Fin n → kˣ) M) {z : M} {ϖ : kˣ} {ξ : Fin n → ℂˣ} {c : ℂ}
    (hz : z ≠ 0)
    (hx : ∀ x : Fin n → ℤ, StrictAnti x → R (fun i => ϖ ^ x i) z = (c * GlobalTheory.BCT.pw ξ x) • z) :
    c = 1 := by
  have hr := hx (rr n) (rr_anti n)
  have h2 := hx (rr n + rr n) (by
    simpa [two_smul] using rr_smul_anti n (N := 2) (by norm_num))
  have hd : (fun i => ϖ ^ (rr n + rr n) i) = (fun i => ϖ ^ rr n i) * (fun i => ϖ ^ rr n i) :=
    dg_add ϖ (rr n) (rr n)
  rw [hd, map_mul, Module.End.mul_apply, hr, map_smul, hr, smul_smul, pw_add] at h2
  set p := GlobalTheory.BCT.pw ξ (rr n)
  have hp : p ≠ 0 := pw_ne_zero ξ _
  have h3 : c * p * (c * p) = c * (p * p) := smul_left_injective ℂ hz h2
  have hc : c ≠ 0 := by
    rintro rfl
    apply hz
    have h4 : R (fun i => ϖ ^ rr n i) z = 0 := by simpa using hr
    have h5 := congrArg (R (fun i => ϖ ^ rr n i)⁻¹) h4
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, map_zero] at h5
    simpa using h5
  have hpp : p * p ≠ 0 := mul_ne_zero hp hp
  apply mul_left_cancel₀ (mul_ne_zero hc hpp)
  linear_combination h3

theorem eig_all (R : Representation ℂ (Fin n → kˣ) M) {z : M} {ϖ : kˣ} {ξ : Fin n → ℂˣ}
    (hx : ∀ x : Fin n → ℤ, StrictAnti x → R (fun i => ϖ ^ x i) z = GlobalTheory.BCT.pw ξ x • z)
    (e : Fin n → ℤ) : R (dg ϖ e) z = GlobalTheory.BCT.pw ξ e • z := by
  obtain ⟨N, hN, ha⟩ := add_anti e
  have hy := hx _ (rr_smul_anti n hN)
  have hxy := hx _ ha
  have hd : (fun i => ϖ ^ (e + N • rr n) i) = dg ϖ e * (fun i => ϖ ^ (N • rr n) i) :=
    dg_add ϖ e _
  rw [hd, map_mul, Module.End.mul_apply, hy, map_smul, pw_add, mul_comm, mul_smul] at hxy
  exact smul_right_injective M (pw_ne_zero ξ (N • rr n)) hxy

theorem extChar : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : ℕ) (M : Type) [AddCommGroup M] [Module ℂ M]
    (R : Representation ℂ (Fin n → kˣ) M) (z : M) (ϖ : kˣ) (ξ : Fin n → ℂˣ) (c : ℂ),
    z ≠ 0 → ord k ϖ = 1 → (∀ t ∈ torusO k (Fin n), R t z = z) →
    (∀ x : Fin n → ℤ, StrictAnti x → R (fun i => ϖ ^ x i) z = (c * GlobalTheory.BCT.pw ξ x) • z) →
    ∀ t : Fin n → kˣ,
      R t z = (((torusChar fun i => unrChar k (ξ i)) t : ℂˣ) : ℂ) • z := by
  intro k _ _ _ _ n M _ _ R z ϖ ξ c hz hϖ hO hx t
  have hc : c = 1 := const_eq_one R hz hx
  subst hc
  simp only [one_mul] at hx
  set e : Fin n → ℤ := fun i => ord k (t i) with he
  have hu : t * (dg ϖ e)⁻¹ ∈ torusO k (Fin n) := by
    intro i
    apply ord_eq_zero_iff.1
    have h1 : ord k (t i * (ϖ ^ e i)⁻¹) = 0 := by
      have h2 := ord_mul k (t i * (ϖ ^ e i)⁻¹) (ϖ ^ e i)
      rw [inv_mul_cancel_right, ord_zpow, hϖ, mul_one] at h2
      have h3 : e i = ord k (t i) := rfl
      omega
    simpa [dg] using h1
  have ht : t = dg ϖ e * (t * (dg ϖ e)⁻¹) := by simp
  have h1 : R t z = R (dg ϖ e) z := by
    conv_lhs => rw [ht]
    rw [map_mul, Module.End.mul_apply, hO _ hu]
  rw [h1, eig_all R hx e, torusChar_apply]
  congr 1
  simp [GlobalTheory.BCT.pw, he, unrChar_apply]

end GlobalTheory.CompanionTheory.ExtCharU
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DecompositionGroupLocalGalois
section
open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate
open GroundTheory.ProfCoh GroundTheory.LocalField ValuativeRel CategoryTheory

noncomputable section

namespace GlobalTheory.CompanionTheory.Dict

theorem isFrob_of_unramifiedDegree_eq_one : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)) [IsSepClosure (v.adicCompletion F) (AlgebraicClosure (v.adicCompletion F))], IsPlaceOver A v → ∀ (ι : Ω →ₐ[F] AlgebraicClosure (v.adicCompletion F)) (σ : G F Ω) (g : Gal(AlgebraicClosure (v.adicCompletion F)/v.adicCompletion F)), σ ∈ Dec (F := F) A → (∀ x, ι (σ x) = g (ι x)) → unramifiedDegree (v.adicCompletion F) (AlgebraicClosure (v.adicCompletion F)) g = Multiplicative.ofAdd 1 → IsFrob (F := F) A (normV v) σ := by
  intro F Ω _ _ _ _ _ A v _ hA ι σ g hσ hι hg
  refine (GlobalTheory.FrobTeich.isFrob_iff_teichmuller F Ω A v hA σ).2 ⟨hσ, fun z m hm hz => ?_⟩
  have hcard : Nat.card 𝓀[v.adicCompletion F] = normV v := by
    rw [GroundTheory.Global.natCard_residueField_adicCompletion, Ideal.absNorm_apply,
      Submodule.cardQuot_apply]
    rfl
  have hfrob := (unramifiedDegree_eq_ofAdd_one_iff g).1 hg
  rw [hcard] at hfrob
  have hq : 1 < normV v := hcard ▸ one_lt_card_residueField (v.adicCompletion F)
  suffices h : ι (σ z) = ι (z ^ normV v) from (RingHom.injective ι.toRingHom) h
  rw [hι, map_pow]
  have hξ : (ι z) ^ normV v ^ m = ι z := by rw [← map_pow, hz]
  by_cases h0 : ι z = 0
  · rw [h0, map_zero, zero_pow (by omega)]
  · refine hfrob _ ⟨m, hm.ne', mul_right_cancel₀ h0 ?_⟩
    have e : normV v ^ m = (normV v ^ m - 1) + 1 :=
      (Nat.sub_add_cancel (Nat.one_le_pow _ _ (by omega))).symm
    rw [hcard, ← pow_succ, ← e, hξ, one_mul]

end GlobalTheory.CompanionTheory.Dict
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetHeckeConditionHoldsStatement
section
open GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel PositivityTheory.Lbc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacquet_hecke_condition_holds : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], PositivityTheory.Lbc.CH k := by
  first | exact @GlobalTheory.CompanionTheory.HeckeExist.exists_heckeOp | exact GlobalTheory.CompanionTheory.HeckeExist.exists_heckeOp | (intros; apply GlobalTheory.CompanionTheory.HeckeExist.exists_heckeOp <;> assumption)
end

