import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoeffZeroNeOfMonicIrr
import Formalism.SharpRestriction.Divisibility.PrimeDegreeVariant
import Formalism.LocalToGlobal.Columns.Bundle0002
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IrreducibleCharacterSeries.Bundle0001
import Formalism.LocalToGlobal.Divisibility.ProjLemmas
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0012
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0513
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0603
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1572
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1566
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0952
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0016
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0620
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0665
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0959
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1571
import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0024
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0066
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1461
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1573
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TautologicalInnerProductLift
import Development.AbelianVarietyTheory.Definitions.Divisors.MemSmallSecTrivShift
import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodCharacterPlacewiseCuspidalParabolicProduct
section
noncomputable section

open Formalism.BasicNotions Formalism.L2.DIV Formalism.IndefR.Links NumberField

namespace GlobalTheory.GoodCharProd

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem isIrrChar_of_abs {G K : Type} [Group G] [Fintype G] [Field K] [CharZero K] (σ : K →+* ℂ) {χ : G → K}
    (h : IsAbsIrrChar χ) : Formalism.L2.NT.IsIrrChar (fun g => σ (χ g)) := by
  classical
  obtain ⟨n, ρ, hρ, hχ⟩ := h
  letI : Algebra K ℂ := σ.toAlgebra
  let ι : AlgebraicClosure K →ₐ[K] ℂ := IsAlgClosed.lift
  have hι : ∀ x : K, ι (algebraMap K (AlgebraicClosure K) x) = σ x := fun x => ι.commutes x
  have hch : ∀ g, ρ.character g = Matrix.trace (LinearMap.toMatrix' (ρ g)) := fun g => by
    rw [Representation.character, LinearMap.trace_eq_matrix_trace _ (Pi.basisFun _ (Fin n)),
      LinearMap.toMatrix_eq_toMatrix']
  let ρm : G →* GL (Fin n) (AlgebraicClosure K) :=
    MonoidHom.toHomUnits ((LinearMap.toMatrixAlgEquiv' : Module.End (AlgebraicClosure K) (Fin n → AlgebraicClosure K)
      ≃ₐ[AlgebraicClosure K] Matrix (Fin n) (Fin n) (AlgebraicClosure K)).toRingEquiv.toMonoidHom.comp ρ)
  let ρc : G →* GL (Fin n) ℂ := (Matrix.GeneralLinearGroup.map (ι : AlgebraicClosure K →+* ℂ)).comp ρm
  have htr : ∀ g, Matrix.trace (ρc g : Matrix (Fin n) (Fin n) ℂ) = σ (χ g) := fun g => by
    rw [← hι, ← hχ g, hch g]
    simp [ρc, ρm, Matrix.trace, Matrix.diag, map_sum]
  have hC : ∀ g, star (σ (χ g)) = σ (χ g⁻¹) := fun g => by
    have := PI.SerBridgeGLW.conjugate_character_formula G (PI.SerBridgeGLW.repOfGL ρc) g
    rwa [PI.SerBridgeGLW.repOfGL_character, PI.SerBridgeGLW.repOfGL_character, htr, htr] at this
  refine ⟨⟨n, ρc, fun g => (htr g).symm⟩, ?_⟩
  have horth := Formalism.L2.Col.gx_orth (G := G) (k := AlgebraicClosure K) (ψ := ρ.character) (ψ' := ρ.character)
    ⟨n, ρ, hρ, rfl⟩ ⟨n, ρ, hρ, rfl⟩
  rw [if_pos rfl] at horth
  have hcard : (Nat.card G : AlgebraicClosure K) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hsum : ∑ g, ρ.character g * ρ.character g⁻¹ = (Nat.card G : AlgebraicClosure K) := by
    rw [← mul_one (Nat.card G : AlgebraicClosure K), ← horth, ← mul_assoc, mul_inv_cancel₀ hcard, one_mul]
  unfold Formalism.L2.NT.ipG
  simp only [hC]
  have := congrArg ι hsum
  rw [map_sum, map_natCast, Nat.card_eq_fintype_card] at this
  rw [← this]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [map_mul, hχ, hχ, hι, hι]

theorem isIrrChar_comp {G G' : Type} [Group G] [Fintype G] [Group G'] [Fintype G'] (e : G' ≃* G) {χ : G → ℂ}
    (h : Formalism.L2.NT.IsIrrChar χ) : Formalism.L2.NT.IsIrrChar fun x => χ (e x) := by
  obtain ⟨⟨n, ρ, hρ⟩, hip⟩ := h
  refine ⟨⟨n, ρ.comp e.toMonoidHom, fun x => hρ _⟩, ?_⟩
  unfold Formalism.L2.NT.ipG at hip ⊢
  rw [Fintype.card_congr e.toEquiv, ← hip]
  exact Fintype.sum_equiv e.toEquiv _ _ fun _ => rfl

theorem isProdCuspChar_good : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.grp_record → (∀ k : Fin 2, haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩; ∃ (C : Formalism.IrreducibleCountingLemmas.TYPES.LabelConv (ZMod (D.host.g k))) (O : Formalism.IrreducibleCountingLemmas.TYPES.LabelMap (ZMod (D.host.g k)) C), ∀ f, D.ntypes.eSer k f = Formalism.L2.NT.eSerO O D.R.r f) → (∀ χ ∈ A.X, IsAbsIrrChar χ) → ∀ χ ∈ A.X, GlobalTheory.IndefiniteRowSideFullHecke.CuspidalProductMultiplicity.IsProdCuspChar D.what₂.embLL R.Pg D.R.r fun g => χ (R.eG.symm g) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R hrec hE hX χ hχ
  classical
  obtain ⟨eR, plg, iso, h1, -, h2⟩ := hrec
  letI : Fintype (G0g D.nd) := Fintype.ofEquiv G eR.toEquiv
  have hirr : Formalism.L2.NT.IsIrrChar fun x : G0g D.nd => D.what₂.embLL (χ (eR.symm x)) :=
    isIrrChar_comp eR.symm (isIrrChar_of_abs D.what₂.embLL (hX χ hχ))
  have he0 : ∑ x : G0g D.nd, D.ntypes.e0.coeff x * D.what₂.embLL (χ (eR.symm x)) = D.what₂.embLL (χ (eR.symm 1)) := by
    have h0 := congrArg D.what₂.embLL (GlobalTheory.IdemChar.sum_coeff_idemOf_mul D.what₂.LL G A.X hX χ hχ)
    rw [map_sum] at h0
    rw [map_one, ← h0]
    symm
    refine Fintype.sum_equiv eR.toEquiv _ _ fun g => ?_
    simp [h1]
  obtain ⟨θ, hθ, hχθ⟩ := GlobalTheory.T.irreducible_character_good_idempotent_cuspidal_product' D hE _ hirr he0
  have key : ∀ PP : R.Pg, ∃ θ' : GL (Fin D.R.r) (kP PP.1) → ℂ,
      @GlobalTheory.IndefiniteRowSideFullHecke.CuspidalProductMultiplicity.IsCuspProdChar (kP PP.1) (Ideal.Quotient.field PP.1.asIdeal) D.R.r θ' ∧
        ∀ g, θ' (R.eG g PP) = θ (plg.symm PP) (eR g (plg.symm PP)) := by
    intro PP
    obtain ⟨kv, rfl⟩ := plg.surjective PP
    haveI : Fact (D.host.g kv.1).Prime := ⟨D.host.g_prime kv.1⟩
    letI := Ideal.Quotient.field (plg kv).1.asIdeal
    refine ⟨_, GlobalTheory.FinGL.Transport.isCuspProdChar_transport _ _ (iso kv) _ _ (hθ kv), fun g => ?_⟩
    rw [Equiv.symm_apply_apply, h2]
    exact congrArg _ ((GlobalTheory.FinGL.Transport.glEquiv (iso kv) D.R.r).symm_apply_apply _)
  choose θ' hθ' hθ'' using key
  refine ⟨θ', hθ', fun x => ?_⟩
  obtain ⟨g, rfl⟩ := R.eG.surjective x
  simp only [hθ'', MulEquiv.symm_apply_apply]
  have h3 := hχθ (eR g)
  rw [MulEquiv.symm_apply_apply] at h3
  rw [h3]
  exact (Fintype.prod_equiv plg.symm _ _ fun _ => rfl).symm

end GlobalTheory.GoodCharProd

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorInverseHeckeTranslatesForgetLevel
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke

noncomputable section

namespace GlobalTheory.UPel.HT.Hecke.Comp

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {S : Scheme.{0}}

theorem eta_nsmul {M : ℕ} {s : S ⟶ Sp R} (o : Obj b M s) (n : ℕ) (x : D.La) :
    o.eta (n • x) = o.eta x ^ n := by
  induction n with
  | zero => rw [zero_smul, pow_zero, eta_zero]
  | succ n ih => rw [succ_nsmul, o.eta_add, ih, pow_succ]

theorem transl_one' {A : Over S} [GrpObj A] : transl (1 : 𝟙_ (Over S) ⟶ A) = 𝟙 A := by
  rw [transl, comp_one, _root_.mul_one]

theorem comp_transl {T A : Over S} [GrpObj A] (y : T ⟶ A) (a : 𝟙_ (Over S) ⟶ A) :
    y ≫ transl a = y * (toUnit T ≫ a) := by
  rw [transl, comp_mul, Category.comp_id, ← Category.assoc, comp_toUnit]

theorem transl_mul' {A : Over S} [GrpObj A] (a c : 𝟙_ (Over S) ⟶ A) :
    transl (a * c) = transl a ≫ transl c := by
  rw [comp_transl, transl, transl, comp_mul, _root_.mul_assoc]

theorem transl_pow {A : Over S} [GrpObj A] [IsCommMonObj A] (a : 𝟙_ (Over S) ⟶ A) (k : ℕ) (ha : a ^ k = 1) :
    transl a ≫ ((𝟙 A) ^ k) = (𝟙 A) ^ k := by
  rw [comp_pow, Category.comp_id, transl, mul_pow, ← comp_pow, ha, comp_one, _root_.mul_one]

theorem isUnit_natCast (b : Base D R) (s : S ⟶ Sp R) (k : ℕ) (hk : k.Coprime p) : IsUnit ((k : ℕ) : Γ(S, ⊤)) := by
  have h1 := (b.unit k hk).map ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ s.appTop).hom
  simpa using h1

end GlobalTheory.UPel.HT.Hecke.Comp

namespace GlobalTheory.UPel.HT.Hecke.Comp

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {S : Scheme.{0}}

theorem pow_eq_one_of_mem {k N : ℕ} {s : S ⟶ Sp R} (o : Obj b (N * k * k) s) (h : 𝟙_ (Over S) ⟶ o.A)
    (hh : h ∈ heckeSub o LinearMap.id (N * k)) : h ^ k = 1 := by
  obtain ⟨x, rfl⟩ := hh
  rw [← eta_nsmul, smul_smul, mul_comm k, o.eta_ker]

theorem isGaloisCover_pow (k N : ℕ) (hk : 0 < k) (hN : 0 < N) (hkp : k.Coprime p) (hNp : N.Coprime p)
    (s : S ⟶ Sp R) (o : Obj b (N * k * k) s)
    (hfib : ∀ (K : Type) [Field K] [IsAlgClosed K] (y y' : Sp K ⟶ o.A.left),
      y ≫ ((𝟙 o.A) ^ k).left = y' ≫ ((𝟙 o.A) ^ k).left →
        ∃! a : heckeSub o LinearMap.id (N * k), y ≫ (transl a.1).left = y') :
    GlobalTheory.ZM.IsGaloisCover (heckeSub o LinearMap.id (N * k)) (fun h => (transl h.1).left) ((𝟙 o.A) ^ k).left := by
  obtain ⟨-, hfin, het, hsurj⟩ := GlobalTheory.abelianScheme_id_pow_finite_etale_surjective S o.A k o.ab
    (isUnit_natCast b s k hkp)
  refine ⟨(heckeSub_finite_free p D R b LinearMap.id k (N * k) hk (Nat.mul_pos hN hk) hkp
      (Nat.Coprime.mul hNp hkp) S s o).1, ?_, ?_, ?_, hfin, het, hsurj, hfib⟩
  · show (transl (1 : 𝟙_ (Over S) ⟶ o.A)).left = 𝟙 _
    rw [transl_one']; rfl
  · intro a c
    show (transl (a.1 * c.1)).left = _
    rw [transl_mul']; rfl
  · intro a
    show (transl a.1 ≫ ((𝟙 o.A) ^ k)).left = _
    rw [transl_pow _ k (pow_eq_one_of_mem o a.1 a.2)]

end GlobalTheory.UPel.HT.Hecke.Comp

namespace GlobalTheory.UPel.HT.Hecke.Comp

variable {S : Scheme.{0}}

theorem cls_lbPow' {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) (m : ℕ) (h : (GlobalTheory.UPel.HT.Hecke.lbPow L m).IsLB) :
    GlobalTheory.CechPic.cls (GlobalTheory.UPel.HT.Hecke.lbPow L m) h = m • GlobalTheory.CechPic.cls L hL := by
  refine (GlobalTheory.CechPic.cls_linComb hL _ _ h).trans ?_
  simp [GlobalTheory.CechPic.pull_id]

theorem grpSchemeSquareProductMap_comp {A B C : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] [GrpObj C]
    [IsCommMonObj C] (f : A ⟶ B) (g : B ⟶ C) :
    GlobalTheory.UPel.HT.Hecke.sq2 (f ≫ g) = GlobalTheory.UPel.HT.Hecke.sq2 f ≫ GlobalTheory.UPel.HT.Hecke.sq2 g := by
  simp only [GlobalTheory.UPel.HT.Hecke.sq2, ← Over.comp_left]
  congr 1
  ext <;> simp

theorem grpSchemeSquareProductMap_fst {A B : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] (f : A ⟶ B) :
    GlobalTheory.UPel.HT.Hecke.sq2 f ≫ (fst B B).left = (fst A A).left ≫ f.left := by
  simp only [GlobalTheory.UPel.HT.Hecke.sq2, ← Over.comp_left, lift_fst]

theorem grpSchemeSquareProductMap_snd {A B : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] (f : A ⟶ B) :
    GlobalTheory.UPel.HT.Hecke.sq2 f ≫ (snd B B).left = (snd A A).left ≫ f.left := by
  simp only [GlobalTheory.UPel.HT.Hecke.sq2, ← Over.comp_left, lift_snd]

theorem lift_one_id_grpSchemeSquareProductMap {A B : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] (f : A ⟶ B)
    [IsMonHom f] : (lift (1 : A ⟶ A) (𝟙 A)).left ≫ GlobalTheory.UPel.HT.Hecke.sq2 f = f.left ≫ (lift (1 : B ⟶ B) (𝟙 B)).left := by
  simp only [GlobalTheory.UPel.HT.Hecke.sq2, ← Over.comp_left]
  congr 1
  ext <;> simp

theorem lift_id_one_grpSchemeSquareProductMap {A B : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] (f : A ⟶ B)
    [IsMonHom f] : (lift (𝟙 A) (1 : A ⟶ A)).left ≫ GlobalTheory.UPel.HT.Hecke.sq2 f = f.left ≫ (lift (𝟙 B) (1 : B ⟶ B)).left := by
  simp only [GlobalTheory.UPel.HT.Hecke.sq2, ← Over.comp_left]
  congr 1
  ext <;> simp

end GlobalTheory.UPel.HT.Hecke.Comp

namespace GlobalTheory.UPel.HT.Hecke.Comp

theorem nonempty_objMap_forget : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (g g' : D.La →ₗ[D.O] D.La) (c c' k N : ℕ), k.Coprime p → 3 ≤ N → N.Coprime p → (∀ x, g (g' x) = k • x) → (∀ x, g' (g x) = k • x) → c * c' = k ^ 2 → ∀ (hc : (N * k * k).Coprime p) (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b (N * k * k) s) (o₁ : Obj b (N * k) s) (o₂ : Obj b N s) (ψ₁ : o.A ⟶ o₁.A) (ψ₂ : o₁.A ⟶ o₂.A), IsHecke g' c' k (N * k) o o₁ ψ₁ → IsHecke g c k N o₁ o₂ ψ₂ → Nonempty (ObjMap (o.forget N ⟨k * k, by ring⟩ hc) o₂ (𝟙 S)) := by
  intro p _ D R _ b g g' c c' k N hkp hN3 hNp hgg' hg'g hcc' hc S s o o₁ o₂ ψ₁ ψ₂ h₁ h₂
  obtain ⟨hm₁, ha₁, he₁, hG₁, ⟨hP₁⟩, -⟩ := h₁
  obtain ⟨hm₂, ha₂, he₂, hG₂, ⟨hP₂⟩, -⟩ := h₂
  have hk : 0 < k := Nat.pos_of_ne_zero (by
    rintro rfl; exact (Fact.out : p.Prime).one_lt.ne' ((Nat.coprime_zero_left p).1 hkp))
  have hN : 0 < N := by omega
  have hfibAll : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (k N : ℕ), 0 < k → 0 < N → k.Coprime p → N.Coprime p → ∀ (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b (N * k * k) s) (K : Type) [Field K] [IsAlgClosed K] (y y' : Sp K ⟶ o.A.left), y ≫ ((𝟙 o.A) ^ k).left = y' ≫ ((𝟙 o.A) ^ k).left → ∃! a : GlobalTheory.UPel.HT.Hecke.heckeSub o LinearMap.id (N * k), y ≫ (GlobalTheory.UPel.HT.Hecke.transl a.1).left = y' := GlobalTheory.T.geometric_fibre_mulK_torsor_harrisTaylor
  have hbil : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ P : LB (G2 A).left, P.IsLB → (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → Out.RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left) → ∀ n : ℕ, LBIso (GlobalTheory.UPel.HT.Hecke.lbPow P (n ^ 2)) (P.pull (GlobalTheory.UPel.HT.Hecke.sq2 ((𝟙 A) ^ n))) := GlobalTheory.T.lbIso_lbPow_sq_pull_sq2_of_isGen_of_relAmple
  have hGal := isGaloisCover_pow k N hk hN hkp hNp s o (hfibAll p D R b k N hk hN hkp hNp S s o)
  obtain ⟨hKm, -, -, -⟩ := GlobalTheory.abelianScheme_id_pow_finite_etale_surjective S o.A k o.ab (isUnit_natCast b s k hkp)
  have hχ : ∀ h ∈ heckeSub o LinearMap.id (N * k), h ≫ (ψ₁ ≫ ψ₂) = 1 := by
    rintro _ ⟨x, rfl⟩
    show o.eta ((N * k) • x) ≫ (ψ₁ ≫ ψ₂) = 1
    have e : o.eta ((N * k) • x) ≫ ψ₁ = o₁.eta (N • g x) := by
      rw [he₁, map_nsmul, hg'g, smul_smul]
    rw [← Category.assoc, e]
    exact comp_eq_one_of_transl ψ₂ _ (hG₂.inv ⟨_, mem_heckeSub o₁ g N x⟩)
  obtain ⟨φ, hφm, hφ⟩ := GlobalTheory.HomDescent.exists_desc S o.A o.A o₂.A _ ((𝟙 o.A) ^ k) hKm hGal (ψ₁ ≫ ψ₂)
    inferInstance hχ
  obtain ⟨f₁, hf₁m, hf₁⟩ := GlobalTheory.HomDescent.exists_desc S o.A o₁.A o.A _ ψ₁ hm₁ hG₁ ((𝟙 o.A) ^ k) hKm (by
    rintro _ ⟨x, rfl⟩
    rw [comp_pow, Category.comp_id, ← eta_nsmul, smul_smul, mul_comm k, o.eta_ker])
  obtain ⟨θ, hθm, hθ⟩ := GlobalTheory.HomDescent.exists_desc S o₁.A o₂.A o.A _ ψ₂ hm₂ hG₂ f₁ hf₁m (by
    rintro _ ⟨y, rfl⟩
    rw [he₁, Category.assoc, hf₁, comp_pow, Category.comp_id, ← eta_nsmul, map_nsmul, hg'g, smul_smul, smul_smul,
      mul_comm k N, o.eta_ker])
  have hKe : Epi ((𝟙 o.A) ^ k).left := GlobalTheory.GaloisCartDesc.epi_of_isGaloisCover hGal
  have hKeO : Epi ((𝟙 o.A) ^ k) := (Over.forget S).epi_of_epi_map hKe
  have hχe : Epi (ψ₁ ≫ ψ₂).left := by
    have := GlobalTheory.GaloisCartDesc.epi_of_isGaloisCover hG₁
    have := GlobalTheory.GaloisCartDesc.epi_of_isGaloisCover hG₂
    rw [Over.comp_left]; infer_instance
  have hχeO : Epi (ψ₁ ≫ ψ₂) := (Over.forget S).epi_of_epi_map hχe
  have e1 : φ ≫ θ = 𝟙 o.A := by
    rw [← cancel_epi ((𝟙 o.A) ^ k), ← Category.assoc, hφ, Category.assoc, hθ, hf₁, Category.comp_id]
  have e2 : θ ≫ φ = 𝟙 o₂.A := by
    rw [← cancel_epi (ψ₁ ≫ ψ₂), Category.comp_id, Category.assoc, reassoc_of% hθ, ← Category.assoc, hf₁, hφ]
  let e : o.A ≅ o₂.A := ⟨φ, θ, e1, e2⟩
  haveI : IsMonHom e.hom := hφm
  have hχa : ∀ c0, o.act.act c0 ≫ ψ₁ ≫ ψ₂ = (ψ₁ ≫ ψ₂) ≫ o₂.act.act c0 := fun c0 => by
    rw [reassoc_of% (ha₁ c0), ha₂ c0, Category.assoc]
  have hpol : LBIso o.P (o₂.P.pull (sq2 φ)) := by
    have hQ₂ : (o₂.P.pull (sq2 φ)).IsLB := pull_isLB o₂.isLB _
    have hc0 : 0 < c := Nat.pos_of_ne_zero (by rintro rfl; rw [zero_mul] at hcc'; have := pow_pos hk 2; omega)
    have hc'0 : 0 < c' := Nat.pos_of_ne_zero (by rintro rfl; rw [mul_zero] at hcc'; have := pow_pos hk 2; omega)
    have hcc : k ^ 2 / c * (k ^ 2 / c') = k ^ 2 := by
      rw [Nat.div_eq_of_eq_mul_left hc0 (by rw [← hcc', mul_comm]), Nat.div_eq_of_eq_mul_left hc'0 hcc'.symm,
        mul_comm]
      exact hcc'
    have hL : ∀ m, (GlobalTheory.UPel.HT.Hecke.lbPow o.P m).IsLB := fun m => LB.isLB_linComb o.isLB _ _
    have hL₁ : ∀ m, (GlobalTheory.UPel.HT.Hecke.lbPow o₁.P m).IsLB := fun m => LB.isLB_linComb o₁.isLB _ _
    have E₁ := (GlobalTheory.CechPic.cls_eq_iff (hL _) (pull_isLB o₁.isLB _)).2 hP₁
    have E₂ := (GlobalTheory.CechPic.cls_eq_iff (hL₁ _) (pull_isLB o₂.isLB _)).2 hP₂
    have E₀ := (GlobalTheory.CechPic.cls_eq_iff (hL _) (pull_isLB o.isLB _)).2
      (hbil S o.A o.ab o.P o.isLB o.rig₁ o.rig₂ o.ample k)
    rw [cls_lbPow' o.isLB, GlobalTheory.CechPic.cls_pull o₁.isLB] at E₁
    rw [cls_lbPow' o₁.isLB, GlobalTheory.CechPic.cls_pull o₂.isLB] at E₂
    rw [cls_lbPow' o.isLB, GlobalTheory.CechPic.cls_pull o.isLB] at E₀
    have c2₁ : GlobalTheory.CechPic.pull (lift (1 : o₂.A ⟶ o₂.A) (𝟙 _)).left (GlobalTheory.CechPic.cls o₂.P o₂.isLB) = 0 := by
      rw [← GlobalTheory.CechPic.cls_pull o₂.isLB _ (pull_isLB o₂.isLB _)]
      exact (GlobalTheory.CechPic.cls_eq_zero_iff _).2 o₂.rig₁
    have c2₂ : GlobalTheory.CechPic.pull (lift (𝟙 _) (1 : o₂.A ⟶ o₂.A)).left (GlobalTheory.CechPic.cls o₂.P o₂.isLB) = 0 := by
      rw [← GlobalTheory.CechPic.cls_pull o₂.isLB _ (pull_isLB o₂.isLB _)]
      exact (GlobalTheory.CechPic.cls_eq_zero_iff _).2 o₂.rig₂
    refine GlobalTheory.T.pullback_prod_injective_birigidified_galois_isogeny S o.A o.A _ ((𝟙 o.A) ^ k) o.ab o.ab hKm hGal o.P _ o.isLB hQ₂ o.rig₁ o.rig₂ ?_ ?_ ?_
    · refine (GlobalTheory.CechPic.cls_eq_zero_iff (pull_isLB hQ₂ _)).1 ?_
      rw [GlobalTheory.CechPic.cls_pull hQ₂, GlobalTheory.CechPic.cls_pull o₂.isLB, ← GlobalTheory.CechPic.pull_comp, lift_one_id_grpSchemeSquareProductMap,
        GlobalTheory.CechPic.pull_comp, c2₁, map_zero]
    · refine (GlobalTheory.CechPic.cls_eq_zero_iff (pull_isLB hQ₂ _)).1 ?_
      rw [GlobalTheory.CechPic.cls_pull hQ₂, GlobalTheory.CechPic.cls_pull o₂.isLB, ← GlobalTheory.CechPic.pull_comp, lift_id_one_grpSchemeSquareProductMap,
        GlobalTheory.CechPic.pull_comp, c2₂, map_zero]
    · refine (GlobalTheory.CechPic.cls_eq_iff (pull_isLB o.isLB _) (pull_isLB hQ₂ _)).1 ?_
      rw [GlobalTheory.CechPic.cls_pull o.isLB, GlobalTheory.CechPic.cls_pull hQ₂, GlobalTheory.CechPic.cls_pull o₂.isLB,
        ← GlobalTheory.CechPic.pull_comp, ← grpSchemeSquareProductMap_comp, hφ, grpSchemeSquareProductMap_comp, GlobalTheory.CechPic.pull_comp, ← E₂, map_nsmul, ← E₁,
        smul_smul, hcc, E₀]
  refine ⟨⟨φ.left, sq2 φ, isGrpPullback_of_iso e, ⟨grpSchemeSquareProductMap_fst φ, grpSchemeSquareProductMap_snd φ⟩, ?_, hpol, ?_⟩⟩
  · intro c0
    show (o.act.act c0).left ≫ φ.left = φ.left ≫ (o₂.act.act c0).left
    rw [← Over.comp_left, ← Over.comp_left]
    congr 1
    haveI := o.act.hom c0
    have hKcomm : ((𝟙 o.A) ^ k) ≫ o.act.act c0 = o.act.act c0 ≫ ((𝟙 o.A) ^ k) := by
      rw [pow_comp, comp_pow, Category.id_comp, Category.comp_id]
    rw [← cancel_epi ((𝟙 o.A) ^ k), ← Category.assoc, hKcomm, Category.assoc, hφ, hχa, ← hφ,
      Category.assoc]
  · intro y
    show (o.eta (((N * k * k) / N) • y)).left ≫ φ.left = 𝟙 S ≫ (o₂.eta y).left
    have hd : N * k * k / N = k * k := by rw [_root_.mul_assoc, Nat.mul_div_cancel_left _ hN]
    rw [hd, Category.id_comp, ← Over.comp_left]
    congr 1
    rw [he₂, he₁, hg'g, Category.assoc, ← hφ, ← Category.assoc, comp_pow, Category.comp_id, ← eta_nsmul, smul_smul]

end GlobalTheory.UPel.HT.Hecke.Comp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorObjectMapsComposeCancelStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harris_taylor_object_maps_compose_cancel : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (S₁ S₂ S₃ : Scheme.{0}) (s₁ : S₁ ⟶ Sp R) (s₂ : S₂ ⟶ Sp R) (s₃ : S₃ ⟶ Sp R) (o₁ : GlobalTheory.UPel.HT.Obj b N s₁) (o₂ : GlobalTheory.UPel.HT.Obj b N s₂) (o₃ : GlobalTheory.UPel.HT.Obj b N s₃) (f : S₁ ⟶ S₂) (g : S₂ ⟶ S₃), (Nonempty (GlobalTheory.UPel.HT.ObjMap o₁ o₂ f) → Nonempty (GlobalTheory.UPel.HT.ObjMap o₂ o₃ g) → Nonempty (GlobalTheory.UPel.HT.ObjMap o₁ o₃ (f ≫ g))) ∧ (Nonempty (GlobalTheory.UPel.HT.ObjMap o₁ o₃ (f ≫ g)) → Nonempty (GlobalTheory.UPel.HT.ObjMap o₂ o₃ g) → Nonempty (GlobalTheory.UPel.HT.ObjMap o₁ o₂ f)) := by
  first | exact @GlobalTheory.UPel.HT.objMap_comp_cancel | exact GlobalTheory.UPel.HT.objMap_comp_cancel | (intros; apply GlobalTheory.UPel.HT.objMap_comp_cancel <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorObjectPullbackCompDiagonalBundle
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT

namespace GlobalTheory.UPel.HT.DiagComp

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}
  {S S' : Scheme.{0}} {s : S ⟶ Sp R} {s' : S' ⟶ Sp R} {o : Obj b N s} {o' : Obj b N s'} {f : S' ⟶ S}

theorem diag_comp (m : ObjMap o' o f) :
    (lift (𝟙 o'.A) (𝟙 o'.A)).left ≫ m.φ₂ = m.φ ≫ (lift (𝟙 o.A) (𝟙 o.A)).left := by
  apply pullback.hom_ext
  · have h1 := m.sq.1
    have e1 : (lift (𝟙 o'.A) (𝟙 o'.A)).left ≫ (fst o'.A o'.A).left = 𝟙 _ :=
      congrArg (fun z => z.left) (lift_fst (𝟙 o'.A) (𝟙 o'.A))
    have e2 : (lift (𝟙 o.A) (𝟙 o.A)).left ≫ (fst o.A o.A).left = 𝟙 _ :=
      congrArg (fun z => z.left) (lift_fst (𝟙 o.A) (𝟙 o.A))
    show _ ≫ (fst o.A o.A).left = _ ≫ (fst o.A o.A).left
    rw [Category.assoc, h1, ← Category.assoc, e1, Category.assoc, e2, Category.id_comp, Category.comp_id]
  · have h2 := m.sq.2
    have e1 : (lift (𝟙 o'.A) (𝟙 o'.A)).left ≫ (snd o'.A o'.A).left = 𝟙 _ :=
      congrArg (fun z => z.left) (lift_snd (𝟙 o'.A) (𝟙 o'.A))
    have e2 : (lift (𝟙 o.A) (𝟙 o.A)).left ≫ (snd o.A o.A).left = 𝟙 _ :=
      congrArg (fun z => z.left) (lift_snd (𝟙 o.A) (𝟙 o.A))
    show _ ≫ (snd o.A o.A).left = _ ≫ (snd o.A o.A).left
    rw [Category.assoc, h2, ← Category.assoc, e1, Category.assoc, e2, Category.id_comp, Category.comp_id]

theorem diag_lbIso (m : ObjMap o' o f) :
    LBIso (o'.P.pull (lift (𝟙 o'.A) (𝟙 o'.A)).left) ((o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left).pull m.φ) := by
  have h₁ : LBIso (o'.P.pull (lift (𝟙 o'.A) (𝟙 o'.A)).left) (o.P.pull (m.φ ≫ (lift (𝟙 o.A) (𝟙 o.A)).left)) :=
    MapComp.lbIso_pull_comp m.pol _ (diag_comp m).symm
  have h₂ : LBIso ((o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left).pull m.φ)
      (o.P.pull (m.φ ≫ (lift (𝟙 o.A) (𝟙 o.A)).left)) :=
    MapComp.lbIso_pull_comp (GlobalTheory.PolBaseChange.lbIso_refl (pull_isLB o.isLB _)) m.φ rfl
  exact LBIso.trans (pull_isLB o'.isLB _) (pull_isLB o.isLB _) (pull_isLB (pull_isLB o.isLB _) _) h₁ h₂.symm

end GlobalTheory.UPel.HT.DiagComp

namespace GlobalTheory.UPel.HT

theorem objMap_comp_diag_lbIso : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (S S' S'' : Scheme.{0}) (s : S ⟶ Sp R) (s' : S' ⟶ Sp R) (s'' : S'' ⟶ Sp R) (o : Obj b N s) (o' : Obj b N s') (o'' : Obj b N s'') (f : S' ⟶ S) (f' : S'' ⟶ S'), (Nonempty (ObjMap o'' o' f') → Nonempty (ObjMap o' o f) → Nonempty (ObjMap o'' o (f' ≫ f))) ∧ ∀ m : ObjMap o' o f, LBIso (o'.P.pull (lift (𝟙 o'.A) (𝟙 o'.A)).left) ((o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left).pull m.φ) :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    ⟨fun ⟨m₁⟩ ⟨m₂⟩ => ⟨MapComp.comp m₁ m₂⟩, fun m => DiagComp.diag_lbIso m⟩

end GlobalTheory.UPel.HT
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasIwasawaOfSmul
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling GlobalTheory.ThK.DblKer

noncomputable section
namespace GlobalTheory.SkewDblIwasawa

theorem mem_hR_smul_iff {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    (σ : E →ₐ[F] E) {M : ℕ} (c : E) (hc : c ≠ 0) (Q : Matrix (Fin M) (Fin M) E) (g : GL (Fin M) (R ⊗[F] E)) :
    g ∈ HR R σ (c • Q) ↔ g ∈ HR R σ Q := by
  have hu : IsUnit (inclR (F := F) R c) := (IsUnit.mk0 c hc).map _
  have e : JR (F := F) R (c • Q) = inclR (F := F) R c • JR R Q := by
    ext i j; simp [JR, Matrix.map_apply, Matrix.smul_apply, map_mul]
  change Formalism.UG.cT (sigR R σ) (g : Matrix (Fin M) (Fin M) (R ⊗[F] E)) * JR (F := F) R (c • Q) *
      (g : Matrix (Fin M) (Fin M) (R ⊗[F] E)) = JR (F := F) R (c • Q) ↔
    Formalism.UG.cT (sigR R σ) (g : Matrix (Fin M) (Fin M) (R ⊗[F] E)) * JR (F := F) R Q *
      (g : Matrix (Fin M) (Fin M) (R ⊗[F] E)) = JR (F := F) R Q
  rw [e, Matrix.mul_smul, Matrix.smul_mul, hu.smul_left_cancel]

theorem hasIwasawa_of_smul {F E : Type} [Field F] [Field E] [Algebra F E] {R : Type} [CommRing R] [Algebra F R]
    (σ : E →ₐ[F] E) {n : ℕ} (c : E) (hc : c ≠ 0) (Q : Matrix (Fin (n + n)) (Fin (n + n)) E)
    (S : Subgroup (GL (Fin (n + n)) (R ⊗[F] E)))
    (h : HasIwasawa σ (c • Q) (S.comap (GlobalTheory.AdelicU.matHom R σ (c • Q)))) :
    HasIwasawa σ Q (S.comap (GlobalTheory.AdelicU.matHom R σ Q)) := by
  intro g
  obtain ⟨p, k, hk, e⟩ := h ⟨g.1, (mem_hR_smul_iff R σ c hc Q g.1).2 g.2⟩
  refine ⟨⟨⟨p.1.1, (mem_hR_smul_iff R σ c hc Q _).1 p.1.2⟩, p.2⟩, ⟨k.1, (mem_hR_smul_iff R σ c hc Q _).1 k.2⟩, hk, ?_⟩
  apply Subtype.ext
  have := congrArg Subtype.val e
  exact this

theorem dblGram_smul {E : Type} [Field E] {n : ℕ} (c : E) (J : Matrix (Fin n) (Fin n) E) :
    dblGram finSumFinEquiv (c • J) = c • dblGram finSumFinEquiv J := by
  ext i j
  obtain ⟨i | i, rfl⟩ := finSumFinEquiv.surjective i <;> obtain ⟨j | j, rfl⟩ := finSumFinEquiv.surjective j <;>
    simp only [dblGram, blkMat, Matrix.smul_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply,
      Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
      Matrix.zero_apply, Matrix.neg_apply, smul_zero, smul_neg]

end GlobalTheory.SkewDblIwasawa

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeadLApply
section
set_option autoImplicit false

noncomputable section

open Set MeasureTheory
open ReciprocityTheory.L2DbarEstimates (V)

namespace GlobalTheory.LocFub

open GlobalTheory.CxForm

def headL (n : ℕ) : V (n + 1) →L[ℂ] V n :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin n => ℂ)).symm.toContinuousLinearMap.comp
    ((ContinuousLinearMap.pi fun a : Fin n => ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (n + 1) => ℂ)
      (Fin.castSucc a)).comp (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin (n + 1) => ℂ)).toContinuousLinearMap)

def fibL (n : ℕ) : V 1 →L[ℂ] V (n + 1) :=
  (EuclideanSpace.proj (0 : Fin 1) : V 1 →L[ℂ] ℂ).smulRight (EuclideanSpace.single (Fin.last n) (1 : ℂ))

theorem headL_apply {n : ℕ} (v : V (n + 1)) (a : Fin n) : headL n v a = v (Fin.castSucc a) := rfl

theorem fibL_apply {n : ℕ} (v : V 1) : fibL n v = EuclideanSpace.single (Fin.last n) (v 0) := by
  ext a; simp [fibL, EuclideanSpace.single_apply]

variable {M : Type} [TopologicalSpace M]

def pbDensC {m k : ℕ} (A : HolAtlas M m) (α : A.Fld) (Ψ : V k → M) (v : V k) : ℂ :=
  dens (pull (fderiv ℂ (A.e (A.cover (Ψ v)).choose ∘ Ψ) v)
    (α ⟨((A.cover (Ψ v)).choose, Ψ v), (A.cover (Ψ v)).choose_spec⟩))

def pbDens {m k : ℕ} (A : HolAtlas M m) (α : A.Fld) (Ψ : V k → M) (v : V k) : ℝ := (pbDensC A α Ψ v).re

def fibDensC {m : ℕ} (A : HolAtlas M m) (α : A.Fld) (φ : ℂ → M) (x : ℂ) : ℂ :=
  dens (pull ((fderiv ℂ (A.e (A.cover (φ x)).choose ∘ φ) x).comp (EuclideanSpace.proj (0 : Fin 1) : V 1 →L[ℂ] ℂ))
    (α ⟨((A.cover (φ x)).choose, φ x), (A.cover (φ x)).choose_spec⟩))

def fibDens {m : ℕ} (A : HolAtlas M m) (α : A.Fld) (φ : ℂ → M) (x : ℂ) : ℝ := (fibDensC A α φ x).re

def prodMap {N : Type} [TopologicalSpace N] {n : ℕ} (A : HolAtlas N n) (i : A.ι) (Φ : N → ℂ → M) (v : V (n + 1)) : M :=
  Φ ((A.e i).symm (headL n v)) (v (Fin.last n))

end GlobalTheory.LocFub
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianMatrixGreenValueStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_matrix_green_value : ∀ v : ReciprocityTheory.L2DbarEstimates.V 1, 2 * diagVal (extTrace (fun w : ReciprocityTheory.L2DbarEstimates.V 1 => (Matrix.fromBlocks (Matrix.of fun _ _ => 1 + w 0 * starRingEnd ℂ (w 0)) (Matrix.of fun _ _ => w 0) (Matrix.of fun _ _ => starRingEnd ℂ (w 0)) 1 : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℂ)) v) (EuclideanSpace.single 0 1) = 1 / Real.pi * (ArithHeightModel.u v ^ 2)⁻¹ := by
  first | exact @GlobalTheory.TautDensity.density_eq | exact GlobalTheory.TautDensity.density_eq | (intros; apply GlobalTheory.TautDensity.density_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianSpaceAddSignatureExistsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links GlobalTheory.ChiGrid
open IsDedekindDomain NumberField Matrix
open scoped TensorProduct nonZeroDivisors Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_space_add_signature_exists : ∀ (D : D7) (A : HSp D) (p q c : ℕ) (neg : Bool), A.SigOK → (∀ τ, A.sig τ = (p, q)) → ∃ B : HSp D, Nonempty (HermitianOrthogonalExtensionData A B c (if neg then -1 else 1)) ∧ B.SigOK ∧ ∀ τ, B.sig τ = (p + (if neg then c / 2 else (c + 1) / 2), q + (if neg then (c + 1) / 2 else c / 2)) := by
  first | exact @GlobalTheory.SignatureAddition.exists_hermitian_space_add_signature | exact GlobalTheory.SignatureAddition.exists_hermitian_space_add_signature | (intros; apply GlobalTheory.SignatureAddition.exists_hermitian_space_add_signature <;> assumption)
end

