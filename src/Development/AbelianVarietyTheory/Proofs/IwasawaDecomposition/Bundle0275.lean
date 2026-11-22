import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StdLvPr
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0269
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0270
import Formalism.LocalToGlobal.Columns.TiedLv
import Formalism.LocalToGlobal.Columns.Bundle0032
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0260
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0119
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Formalism.LocalRingCardinality.Bundle0005
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0178
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0189
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0170
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0333
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0135
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsSplittingCharacterSelf
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0221
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0261
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0259

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DecoStabTrivial
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.TwAtStd

theorem ptY_mv_deco {X : Fields} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 X.E))} {y : Ys X n}
    (p : PtY ST SG Q y) (d : DecoSet X.E n ST SG)
    (h1 : ∀ (P : Q) (x : Sp X.E n), p.1.1.1.2 P x ∈ d.1.at P.1 ↔ x ∈ stdAt X.E n P.1) (h2 : p.1.2 ∈ y.ys d.1.N) :
    (p.mv d).1.1.deco = d := by
  have e : p.mv d = (⟨(⟨(d, p.1.1.1.2), h1⟩, p.1.2), h2⟩ : PtY ST SG Q y) := dif_pos ⟨h1, h2⟩
  rw [e]
  rfl

theorem diaPt_deco (B : Base) (X : PreX B.toPre) (I : TC B X) (u : B.Word) (a : I.ι) (i : ℕ)
    (P : (B.primes X).vT u) (x : (Res P.1)ˣ) (c : (I.stp u a i).Cl) :
    (((I.atIn u a).A i).diaPt P x c).1.1.deco = DecoSet.dia1 P x ((I.stp u a i).rep c).1.1.deco :=
  ptY_mv_deco ((I.stp u a i).rep c) _ (fun Q y => ((I.stp u a i).rep c).1.1.2 Q y) ((I.stp u a i).rep c).2

theorem dil_eCls0 (B : Base) (X : PreX B.toPre) (I : TC B X) (hI : I.Ok) (l : I.Laws) (u : B.Word) (a : I.ι)
    (P : (B.primes X).vT u) (x : (Res P.1)ˣ) (c : (I.stp u I.mu0 0).Cl) :
    (I.atIn u a).dil 0 P x (I.eCls0 l u a c) = I.eCls0 l u a ((I.atIn u I.mu0).dil 0 P x c) := by
  show (I.stp u a 0).cl (I.cl0 u a (l.idx0 a).some c).1 (((I.atIn u a).A 0).diaPt P x (I.cl0 u a (l.idx0 a).some c)) =
    I.cl0 u a (l.idx0 a).some ((I.stp u I.mu0 0).cl c.1 (((I.atIn u I.mu0).A 0).diaPt P x c))
  refine (ClsZero.cl_eq_iff hI u a _ _ _ _).2 ?_
  rw [diaPt_deco, ClsZero.stepZero_corresponding_representatives_same_deco hI]
  have e := (ClsZero.cl_eq_iff hI u I.mu0 _ _ _ _).1
    (ClsZero.cl_rep (I.stp u I.mu0 0) ((I.stp u I.mu0 0).cl c.1 (((I.atIn u I.mu0).A 0).diaPt P x c)))
  show _ = ClsZero.canon _ ((I.stp u I.mu0 0).rep ((I.stp u I.mu0 0).cl c.1 (((I.atIn u I.mu0).A 0).diaPt P x c))).1.1.deco
  rw [e, diaPt_deco]

theorem deco_stab_trivial (B : Base) (X : PreX B.toPre) (I : TC B X) (hI : I.Ok) (l : I.Laws) (u : B.Word) (a : I.ι)
    (b : (I.stp u a 0).β) (p : (I.stp u a 0).D b) (γ : UF B.fields.E (B.R.N 0)) (k : GLG B.fields.E (B.R.N 0) (B.primes X).vGs)
    (hk : k ∈ (colLev I.Ch 0).grp) (h : ((γ, k) : UF B.fields.E (B.R.N 0) × GLG B.fields.E (B.R.N 0) (B.primes X).vGs) • p.1.1.deco = p.1.1.deco) :
    γ = 1 ∧ k = 1 := by
  have hfree : (I.stp u a 0).Free := (l.lev u a).free0
  let q : DecoF B.fields.E (B.R.N 0) ((B.primes X).vT u) (B.primes X).vGs (QE I.sel (I.tup a)) :=
    ((γ, k, 1) : UF B.fields.E (B.R.N 0) × GLG B.fields.E (B.R.N 0) (B.primes X).vGs × GLQ B.fields.E (B.R.N 0) (QE I.sel (I.tup a))) • p.1.1
  have hq : q.deco = p.1.1.deco := h
  have hc : ∀ P : QE I.sel (I.tup a), (p.1.1.fr P)⁻¹ * q.fr P ∈ GLint B.fields.E (B.R.N 0) P.1 := by
    intro P x
    have h1 := q.2 P x
    have h2 := p.1.1.2 P ((p.1.1.fr P)⁻¹ (q.fr P x))
    have h3 : p.1.1.1.2 P ((p.1.1.fr P)⁻¹ (q.fr P x)) = q.fr P x := LinearEquiv.apply_symm_apply _ _
    rw [h3] at h2
    have h4 : q.1.1 = p.1.1.1.1 := hq
    rw [h4] at h1
    exact h2.symm.trans h1
  have hkG : k ∈ (levGAt I.sel (I.tup a) (I.idx a) (I.Tp a) 0 b).grp := by rw [ClsZero.levelTypePrimes_stepZero_eq_colLev hI]; exact hk
  let qq : GLQ B.fields.E (B.R.N 0) (QE I.sel (I.tup a)) := fun P => ⟨(p.1.1.fr P)⁻¹ * q.fr P, hc P⟩
  have htop : ∀ Θ : LevQFam B.fields.E B.fields.K (B.R.N 0) (QE I.sel (I.tup a)), Θ = LevQFam.top _ _ _ _ → qq ∈ Θ.grp := by
    rintro _ rfl
    intro P _
    trivial
  have hqQ := htop _ (ClsZero.chartIndexLevelTwistPrimes_stepZero_eq_top hI a b)
  have key : ∀ (y : Ys B.fields (B.R.N 0)), y = Ys.triv _ _ → ∀ (S : Set (Sp B.fields.E (B.R.N 0))) N, S ∈ y.ys N → S = ∅ := by
    rintro _ rfl S N hS
    exact hS
  have hp0 : p.1.2 = ∅ := key _ (ClsZero.ys0 a) _ _ p.2
  let g : (I.stp u a 0).G b := (γ, ⟨k, hkG⟩, ⟨qq, hqQ⟩)
  have hg : (I.stp u a 0).act b g p = p := by
    refine Subtype.ext (Prod.ext (Subtype.ext (Prod.ext h ?_)) ?_)
    · funext P
      show γ.1 * p.1.1.fr P * ((p.1.1.fr P)⁻¹ * (γ.1 * p.1.1.fr P * ((1 : GLQ B.fields.E (B.R.N 0) (QE I.sel (I.tup a))) P)⁻¹.1))⁻¹ = p.1.1.fr P
      simp only [Pi.one_apply, inv_one, OneMemClass.coe_one, mul_one]
      group
    · show (fun v => γ.1 v) '' p.1.2 = p.1.2
      rw [hp0, Set.image_empty]
  have e := hfree b g p hg
  exact ⟨congrArg Prod.fst e, congrArg (fun g : (I.stp u a 0).G b => (g.2.1 : GLG B.fields.E (B.R.N 0) (B.primes X).vGs)) e⟩

theorem chrG_eq {E K : Type} [Field E] [NumberField E] [Field K] {n : ℕ} {SG : Finset (HeightOneSpectrum (𝓞 E))}
    (L Λ Λ' : LevFam E K n SG) (h : Λ = L) (h' : Λ' = L) (k : Λ.grp) (k' : Λ'.grp) (e : k.1 = k'.1) :
    Λ.chr k = Λ'.chr k' := by
  subst h h'
  rw [Subtype.ext e]

theorem chrQ_top {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {n : ℕ} {Q : Finset (HeightOneSpectrum (𝓞 E))}
    (Θ : LevQFam E K n Q) (h : Θ = LevQFam.top E K n Q) (q : Θ.grp) : Θ.chr q = 1 := by
  subst h
  unfold LevQFam.chr piChar
  erw [Finset.prod_eq_one (fun i _ => MonoidHom.one_comp _)]
  rfl

theorem dilT_eCls0 (B : Base) (X : PreX B.toPre) (I : TC B X) (hI : I.Ok) (l : I.Laws) (u : B.Word) (a : I.ι)
    (P : (B.primes X).vT u) (x : (Res P.1)ˣ) (c : (I.stp u I.mu0 0).Cl) :
    (I.atIn u a).dilT B.fields.emb B.embLL 0 P x (I.eCls0 l u a c) = (I.atIn u I.mu0).dilT B.fields.emb B.embLL 0 P x c := by
  show (I.stp u a 0).tr B.fields.emb B.embLL (I.cl0 u a (l.idx0 a).some c).1 ((I.stp u a 0).mv (I.cl0 u a (l.idx0 a).some c).1 (((I.atIn u a).A 0).diaPt P x (I.cl0 u a (l.idx0 a).some c))) = (I.stp u I.mu0 0).tr B.fields.emb B.embLL c.1 ((I.stp u I.mu0 0).mv c.1 (((I.atIn u I.mu0).A 0).diaPt P x c))
  set ga := (I.stp u a 0).mv (I.cl0 u a (l.idx0 a).some c).1 (((I.atIn u a).A 0).diaPt P x (I.cl0 u a (l.idx0 a).some c)) with hga
  set gm := (I.stp u I.mu0 0).mv c.1 (((I.atIn u I.mu0).A 0).diaPt P x c) with hgm
  have hA : ((ga.1, ga.2.1.1) : UF B.fields.E (B.R.N 0) × GLG B.fields.E (B.R.N 0) (B.primes X).vGs) •
      ((I.stp u a 0).rep ((I.stp u a 0).cl (I.cl0 u a (l.idx0 a).some c).1 (((I.atIn u a).A 0).diaPt P x (I.cl0 u a (l.idx0 a).some c)))).1.1.deco = (((I.atIn u a).A 0).diaPt P x (I.cl0 u a (l.idx0 a).some c)).1.1.deco :=
    congrArg (fun p : (I.stp u a 0).D (I.cl0 u a (l.idx0 a).some c).1 => p.1.1.deco) ((I.stp u a 0).mv_smul (I.cl0 u a (l.idx0 a).some c).1 (((I.atIn u a).A 0).diaPt P x (I.cl0 u a (l.idx0 a).some c)))
  have hM : ((gm.1, gm.2.1.1) : UF B.fields.E (B.R.N 0) × GLG B.fields.E (B.R.N 0) (B.primes X).vGs) •
      ((I.stp u I.mu0 0).rep ((I.stp u I.mu0 0).cl c.1 (((I.atIn u I.mu0).A 0).diaPt P x c))).1.1.deco = (((I.atIn u I.mu0).A 0).diaPt P x c).1.1.deco :=
    congrArg (fun p : (I.stp u I.mu0 0).D c.1 => p.1.1.deco) ((I.stp u I.mu0 0).mv_smul c.1 (((I.atIn u I.mu0).A 0).diaPt P x c))
  have hRA : ((I.stp u a 0).rep ((I.stp u a 0).cl (I.cl0 u a (l.idx0 a).some c).1 (((I.atIn u a).A 0).diaPt P x (I.cl0 u a (l.idx0 a).some c)))).1.1.deco = ClsZero.canon (colLev I.Ch 0) (((I.atIn u a).A 0).diaPt P x (I.cl0 u a (l.idx0 a).some c)).1.1.deco :=
    (ClsZero.stepZero_representative_deco_eq_canonical hI u a _).trans ((ClsZero.cl_eq_iff hI u a _ _ _ _).1 (ClsZero.cl_rep (I.stp u a 0) ((I.stp u a 0).cl (I.cl0 u a (l.idx0 a).some c).1 (((I.atIn u a).A 0).diaPt P x (I.cl0 u a (l.idx0 a).some c)))))
  have hRM : ((I.stp u I.mu0 0).rep ((I.stp u I.mu0 0).cl c.1 (((I.atIn u I.mu0).A 0).diaPt P x c))).1.1.deco = ClsZero.canon (colLev I.Ch 0) (((I.atIn u I.mu0).A 0).diaPt P x c).1.1.deco :=
    (ClsZero.stepZero_representative_deco_eq_canonical hI u I.mu0 _).trans ((ClsZero.cl_eq_iff hI u I.mu0 _ _ _ _).1 (ClsZero.cl_rep (I.stp u I.mu0 0) ((I.stp u I.mu0 0).cl c.1 (((I.atIn u I.mu0).A 0).diaPt P x c))))
  have hT : (((I.atIn u a).A 0).diaPt P x (I.cl0 u a (l.idx0 a).some c)).1.1.deco = (((I.atIn u I.mu0).A 0).diaPt P x c).1.1.deco := by
    rw [diaPt_deco, diaPt_deco, ClsZero.stepZero_corresponding_representatives_same_deco hI]
  have hR : ((I.stp u I.mu0 0).rep ((I.stp u I.mu0 0).cl c.1 (((I.atIn u I.mu0).A 0).diaPt P x c))).1.1.deco = ((I.stp u a 0).rep ((I.stp u a 0).cl (I.cl0 u a (l.idx0 a).some c).1 (((I.atIn u a).A 0).diaPt P x (I.cl0 u a (l.idx0 a).some c)))).1.1.deco := by rw [hRA, hRM, hT]
  rw [hR, ← hT] at hM
  have hfix : (((gm.1, gm.2.1.1) : UF B.fields.E (B.R.N 0) × GLG B.fields.E (B.R.N 0) (B.primes X).vGs)⁻¹ *
      ((ga.1, ga.2.1.1) : UF B.fields.E (B.R.N 0) × GLG B.fields.E (B.R.N 0) (B.primes X).vGs)) •
      ((I.stp u a 0).rep ((I.stp u a 0).cl (I.cl0 u a (l.idx0 a).some c).1 (((I.atIn u a).A 0).diaPt P x (I.cl0 u a (l.idx0 a).some c)))).1.1.deco = ((I.stp u a 0).rep ((I.stp u a 0).cl (I.cl0 u a (l.idx0 a).some c).1 (((I.atIn u a).A 0).diaPt P x (I.cl0 u a (l.idx0 a).some c)))).1.1.deco := by
    rw [mul_smul, hA, inv_smul_eq_iff, hM]
  have memG : ∀ Λ : LevFam B.fields.E B.fields.K (B.R.N 0) (B.primes X).vGs, Λ = colLev I.Ch 0 → ∀ k : Λ.grp, k.1 ∈ (colLev I.Ch 0).grp := by
    rintro _ rfl k
    exact k.2
  have hkA := memG _ (ClsZero.levelTypePrimes_stepZero_eq_colLev hI a _) ga.2.1
  have hkM := memG _ (ClsZero.levelTypePrimes_stepZero_eq_colLev hI I.mu0 _) gm.2.1
  obtain ⟨e1, e2⟩ := deco_stab_trivial B X I hI l u a (I.cl0 u a (l.idx0 a).some c).1 ((I.stp u a 0).rep ((I.stp u a 0).cl (I.cl0 u a (l.idx0 a).some c).1 (((I.atIn u a).A 0).diaPt P x (I.cl0 u a (l.idx0 a).some c)))) (gm.1⁻¹ * ga.1) (gm.2.1.1⁻¹ * ga.2.1.1)
    (Subgroup.mul_mem _ (Subgroup.inv_mem _ hkM) hkA) hfix
  have eγ : ga.1 = gm.1 := (inv_mul_eq_one.1 e1).symm
  have ek : ga.2.1.1 = gm.2.1.1 := (inv_mul_eq_one.1 e2).symm
  show trFr B.fields.emb B.embLL ((I.stp u a 0).gam (I.cl0 u a (l.idx0 a).some c).1 ga) ((I.stp u a 0).chr (I.cl0 u a (l.idx0 a).some c).1 ga) = trFr B.fields.emb B.embLL ((I.stp u I.mu0 0).gam c.1 gm) ((I.stp u I.mu0 0).chr c.1 gm)
  congr 1
  · show ufGL _ _ ga.1 = ufGL _ _ gm.1
    rw [eγ]
  · show (levGAt I.sel (I.tup a) (I.idx a) (I.Tp a) 0 (I.cl0 u a (l.idx0 a).some c).1).chr ga.2.1 * (levQAt I.sel (I.tup a) (I.idx a) (I.Tp a) 0 (I.cl0 u a (l.idx0 a).some c).1).chr ga.2.2 =
      (levGAt I.sel (I.tup I.mu0) (I.idx I.mu0) (I.Tp I.mu0) 0 c.1).chr gm.2.1 * (levQAt I.sel (I.tup I.mu0) (I.idx I.mu0) (I.Tp I.mu0) 0 c.1).chr gm.2.2
    rw [chrQ_top _ (ClsZero.chartIndexLevelTwistPrimes_stepZero_eq_top hI a _), chrQ_top _ (ClsZero.chartIndexLevelTwistPrimes_stepZero_eq_top hI I.mu0 _),
      chrG_eq (colLev I.Ch 0) _ _ (ClsZero.levelTypePrimes_stepZero_eq_colLev hI a _) (ClsZero.levelTypePrimes_stepZero_eq_colLev hI I.mu0 _) ga.2.1 gm.2.1 ek]

theorem mem_Fi_of_free {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι]
    {n : ℕ} (S : GStep E K n) (emb : ι → E →+* K) (σ : K →+* ℂ) (lam : ι → DomWeight n) (hS : S.Free)
    (φ : S.Cl → Col2.Fr emb σ n → ℂ) : φ ∈ S.Fi emb σ lam ↔ ∀ c, φ c ∈ ValC (Gr emb σ n) lam := by
  constructor
  · intro h c
    exact (h c).1
  · intro h c
    refine ⟨h c, fun g => ?_⟩
    have hg : g.1 = 1 := hS c.1 g.1 _ g.2
    funext y
    show S.tr emb σ c.1 g.1 (φ c) y = φ c y
    rw [hg]
    simp [GStep.tr, trFr_apply, frMul_one]

set_option maxHeartbeats 1000000 in

theorem twAtT_exists : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (l0 : I.Law0 l) (u : B.Word) (a : I.ι), ∃ t : TwAtT (I.tw l l0 Z) u a, t.eVT = Equiv.refl _ ∧ ∀ v (r : 𝓞 B.host.E), t.eFv v (I.resT l u a v r) = I.resT l u I.mu0 (t.eVT v) r := by
  intro B X I hI hP l Z l0 u a
  refine ⟨
    { eVT := Equiv.refl _
      eFv := fun v => RingEquiv.refl _
      psiT := fun v x => rfl
      rhoT := by
        intro v x φ
        have e1 := dil_eCls0 B X I hI l u a v x
        have e2 := dilT_eCls0 B X I hI l u a v x
        funext c y
        obtain ⟨c', rfl⟩ := (I.eCls0 l u a).surjective c
        show (I.atIn u a).dilT B.fields.emb B.embLL 0 v x (I.eCls0 l u a c') (φ ((I.eCls0 l u a).symm ((I.atIn u a).dil 0 v x (I.eCls0 l u a c')))) y = (I.atIn u I.mu0).dilT B.fields.emb B.embLL 0 v x ((I.eCls0 l u a).symm (I.eCls0 l u a c')) (φ ((I.atIn u I.mu0).dil 0 v x ((I.eCls0 l u a).symm (I.eCls0 l u a c')))) y
        simp only [e1, e2, Equiv.symm_apply_apply]
      Mu0 := by
        show (I.stp u a 0).Fi B.fields.emb B.embLL (lamT (B.hcW u) 0) = Submodule.map (LinearEquiv.funCongrLeft ℂ (Col2.Fr B.fields.emb B.embLL (B.R.N 0) → ℂ) (I.eCls0 l u a).symm).toLinearMap ((I.stp u I.mu0 0).Fi B.fields.emb B.embLL (lamT (B.hcW u) 0))
        rw [Submodule.map_equiv_eq_comap_symm]
        ext ψ
        rw [Submodule.mem_comap, mem_Fi_of_free _ _ _ _ (l.lev u a).free0, mem_Fi_of_free _ _ _ _ (l.lev u I.mu0).free0]
        constructor
        · intro h c
          exact h _
        · intro h c
          obtain ⟨c', rfl⟩ := (I.eCls0 l u a).surjective c
          have := h c'
          simpa using this
      duStar := rfl
      Dstar := rfl
      GamP := rfl
      tauOf := fun w hw v => rfl
      seenP := fun w hw => rfl }, rfl, fun v r => rfl⟩

end GlobalTheory.Mem.Col2.TwAtStd

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DownMoveLocalDualLatticeEqLevelPrime
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.DnLat

theorem locP_congr {R W : Type*} [CommRing R] [AddCommGroup W] [Module R W] {p q : Ideal R} [p.IsPrime] [q.IsPrime]
    (h : p = q) (L : Submodule R W) : Formalism.HermitianLatticesTheory.localization₂ p L = Formalism.HermitianLatticesTheory.localization₂ q L := by
  subst h; rfl

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}

theorem extF_eq (M : Submodule (𝓞 E) (Fin n → E)) (P : HeightOneSpectrum (𝓞 E))
    (g : Module.Dual (Res P) (TDat.Red M P)) (y : Fin n → E) : TDat.extF M P g y = modP.ext P M g y := by
  classical
  unfold TDat.extF
  split_ifs with h
  · obtain ⟨s, hs, z, hz, hgz⟩ := h.choose_spec
    have hsy : s • y ∈ M := hz ▸ z.2
    have e := modP.ext_spec P M g y hs hsy
    have ez : z = ⟨s • y, hsy⟩ := Subtype.ext hz
    subst ez
    apply mul_left_cancel₀ (mk_ne_zero hs)
    rw [e, ← hgz]
    rfl
  · by_cases hy : ∃ s : 𝓞 E, s ∉ P.asIdeal ∧ s • y ∈ M
    · exfalso
      obtain ⟨s, hs, hsy⟩ := hy
      exact h ⟨modP.ext P M g y, s, hs, ⟨s • y, hsy⟩, rfl, (modP.ext_spec P M g y hs hsy).symm⟩
    · unfold modP.ext
      rw [dif_neg hy]

variable {ST SG : Finset (HeightOneSpectrum (𝓞 E))}

theorem ok_dn_extF {d : Deco E n ST SG} (hd : d.Ok) (P : ST) (hP : MoveHyp ST SG P) {M : Submodule (𝓞 E) (Fin n → E)}
    (hM : M = d.dnN P) (g : Module.Dual (Res P.1) (TDat.Red M P.1)) (hg : g ≠ 0) :
    (d.dn P (TDat.extF M P.1 g)).Ok := by
  subst hM
  have e : TDat.extF (d.dnN P) P.1 g = modP.ext P.1 (d.dnN P) g := funext (extF_eq _ _ g)
  rw [e]
  have hF := modP.ext_funAt P.1 (d.dnN P) g
  refine hd.dn P hP hF.add hF.smul hF.off ?_
  obtain ⟨z, hz⟩ : ∃ z, g z ≠ 0 := by
    by_contra H
    push Not at H
    exact hg (LinearMap.ext H)
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  exact ⟨x.1, x.2, by rw [modP.ext_of_mem]; exact hz⟩

theorem locP_Lsh_dn {a : 𝓞 E} (ha : SepElt ST a) {d : Deco E n ST SG} (hd : d.Ok) (P : ST) (hne : conjPrime₂ P.1 ≠ P.1)
    {f' : Sp E n → 𝓞 E ⧸ P.1.asIdeal} (hd' : (d.dn P f').Ok) :
    Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal (d.dn P f').Lsh = Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal d.L := by
  rw [hd'.locP_Lsh ha P]
  show Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal (d.dnN P) = _
  rw [(hd.dnN_spec P hne).2.2.2, tud_locP_L ha ⟨d, hd⟩ P]
  exact le_antisymm
    (localization_le_of_smul_mem (one_notMem P.1) fun x hx => by rw [one_smul]; exact lv_kerAt_le ⟨d, hd⟩ ha P hx)
    (localization_le_of_smul_mem (ha.off P) fun x hx => lv_smul_LshKer_mem ⟨d, hd⟩ ha P hx)

theorem mulLat_Lsh_rep {K : Type} [Field K] [NumberField K] [StarRing K] (S : GStep E K n) (hS : S.Ok) (b : S.β) (d : S.D b)
    {γ : Matrix (Fin n) (Fin n) E} (hγ : γ = (S.gam b (S.mv b d) : Matrix (Fin n) (Fin n) E)) :
    Formalism.L2.Forms.mulLat γ (S.Lsh b (S.rep (S.cl b d))) = S.Lsh b d := by
  subst hγ
  ext x
  unfold Formalism.L2.Forms.mulLat
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    have h := (hS.lsh_smul b (S.mv b d) (S.rep (S.cl b d)) y).2 hy
    rwa [S.mv_smul] at h
  · intro hx
    refine ⟨((S.gam b (S.mv b d))⁻¹ : GL (Fin n) E).1 *ᵥ x, ?_, ?_⟩
    · refine (hS.lsh_smul b (S.mv b d) (S.rep (S.cl b d)) _).1 ?_
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec, S.mv_smul]
      exact hx
    · show (S.gam b (S.mv b d) : Matrix (Fin n) (Fin n) E) *ᵥ (((S.gam b (S.mv b d))⁻¹ : GL (Fin n) E).1 *ᵥ x) = x
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]

end GlobalTheory.Mem.Col2.DnLat

open GlobalTheory.Mem.Col2.DnLat in
set_option maxHeartbeats 1000000 in

theorem GlobalTheory.Mem.Col2.TC.dn_locP_lat : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (i : ℕ) (hi : i ≤ B.R.m) (bad : Set (HeightOneSpectrum (𝓞 B.host.F))) (Ch : Type) (chOf : (I.stp u a i).Cl → Ch) (K : ∀ β : Ch, LevelChart (I.rec7 l Z) (B.T u) bad i hi (fun c : {c // chOf c = β} => (I.chain l u a).stab i c.1) (fun c => latCrd (I.rec7 l Z) i hi (I.latAt u a i c.1))) (eY : (I.chain l u a).Y i ≃ Formalism.L2.Forms.Fr (I.rec7 l Z) i hi) (eV : (I.atT l u a).vT ≃ {v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F) // (B.T u : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal}) (L : LevelCompatibleLattices (D := (I.rec7 l Z)) (I.fm l u a) (B.T u) (I.resT l u a) i hi fun c => latCrd (I.rec7 l Z) i hi (I.latAt u a i c)), I.ReadsK l Z u a i hi chOf K → I.IdY l Z u a i hi eY → I.IdV l u a eV → I.IdL l Z u a i hi L → ∀ (v : (I.atT l u a).vT) (β : Ch) (c : {c // chOf c = β}) (g : Module.Dual (Res v.1) (((I.atIn u a).A i).lk v c.1)), g ≠ 0 → ∀ (γ : UJ (sigD (I.rec7 l Z) : (I.rec7 l Z).host.E →+* (I.rec7 l Z).host.E) (gramN (I.rec7 l Z) i hi)), (γ.1 : GL (Fin (B.R.N i)) B.fields.E) = (I.stp u a i).gam c.1.1 ((I.stp u a i).mv c.1.1 (((I.atIn u a).A i).dnPt v c.1 g)) → Formalism.HermitianLatticesTheory.localization₂ (PvG (I.resT l u a) v) (mulLat γ.1.1 (LdG (I.rec7 l Z) i hi (latCrd (I.rec7 l Z) i hi (I.latAt u a i ((I.fm l u a).dn i v c.1 g))))) = Formalism.HermitianLatticesTheory.localization₂ (PvG (I.resT l u a) v) (latCrd (I.rec7 l Z) i hi (I.latAt u a i c.1)) := by
  intro B X I hI hP l Z u a i hi bad Ch chOf K eY eV L hK hY hV hL v β c g hg γ hγ
  obtain ⟨hg1, -, hcrd⟩ := (GlobalTheory.Mem.Col2.TC.spaces_in_coordinates I hI hP l Z).2.2.2 i hi
  have hlat := (hcrd u a).1
  have hPv : PvG (D := I.rec7 l Z) (I.resT l u a) v = (v.1 : HeightOneSpectrum (𝓞 B.fields.E)).asIdeal := by
    unfold PvG resT
    ext x
    exact Submodule.Quotient.mk_eq_zero _

  rw [@locP_congr _ _ _ _ _ (PvG (D := I.rec7 l Z) (I.resT l u a) v) _ (RingHom.ker_isPrime _) v.1.isPrime hPv, @locP_congr _ _ _ _ _ (PvG (D := I.rec7 l Z) (I.resT l u a) v) _ (RingHom.ker_isPrime _) v.1.isPrime hPv, hlat, hlat]
  have hdual : ∀ M : Submodule (𝓞 (I.rec7 l Z).host.E) (Fin ((I.rec7 l Z).R.N i) → (I.rec7 l Z).host.E),
      LdG (I.rec7 l Z) i hi M = Formalism.HermitianLatticesTheory.dual (hStd (I.rec7 l Z).host.E ((I.rec7 l Z).R.N i)) M := fun M => by
    unfold LdG
    rw [hg1]
    unfold dualL
    exact rlc_span_dualSet (I.rec7 l Z).sp.cm _ M
  have hok : (I.atIn u a).Ok := l.lev u a
  have hT := hok.tied i
  have hSok : (I.stp u a i).Ok := (l.ch u a).step i
  have hmul := mulLat_Lsh_rep (I.stp u a i) hSok c.1.1 (((I.atIn u a).A i).dnPt v c.1 g) (congrArg Units.val hγ)
  have hm := moveHyp_of_ok l.pr u v
  have hMove : MoveHyp ((B.primes X).vT u) ∅ v := ⟨hm.ne, hm.st, fun w => absurd w.2 (Finset.notMem_empty _)⟩
  have hsep := sepElt_of_ok l.pr u
  have hOk := ok_dn_extF (hT.ok c.1.1 ((I.stp u a i).rep c.1)) v hMove (hT.dnN_eq c.1.1 ((I.stp u a i).rep c.1) v) g hg
  have key : Formalism.HermitianLatticesTheory.localization₂ (v.1 : HeightOneSpectrum (𝓞 B.fields.E)).asIdeal
      (Formalism.L2.Forms.mulLat γ.1.1 ((I.stp u a i).Lsh c.1.1
        ((I.stp u a i).rep ((I.stp u a i).cl c.1.1 (((I.atIn u a).A i).dnPt v c.1 g))))) =
      Formalism.HermitianLatticesTheory.localization₂ (v.1 : HeightOneSpectrum (𝓞 B.fields.E)).asIdeal (((I.atIn u a).A i).deco c.1.1 ((I.stp u a i).rep c.1)).L := by
    refine (congrArg (Formalism.HermitianLatticesTheory.localization₂ (v.1 : HeightOneSpectrum (𝓞 B.fields.E)).asIdeal)
      (hmul.trans ((hT.Lsh_eq _ _).trans (congrArg Deco.Lsh (hT.dn_deco _ _ _ _ hOk))))).trans ?_
    exact locP_Lsh_dn hsep (hT.ok _ _) v hMove.ne hOk
  exact (congrArg (fun M => Formalism.HermitianLatticesTheory.localization₂ (v.1 : HeightOneSpectrum (𝓞 B.fields.E)).asIdeal (Formalism.L2.Forms.mulLat γ.1.1 M))
    (hdual _)).trans key
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DualWeylModuleTensorCoefficientUniversalStatement
section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dualWeylModule_tensor_coefficient_universal : ∀ (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n) (V : Type) [AddCommGroup V] [Module ℂ V] (F : MultilinearMap ℂ (fun v => nablaSq ℂ n (lam v)) V), ∃! f : Formalism.L2.DIV.VV ℂ lam →ₗ[ℂ] V, ∀ u, f (GlobalTheory.CoefIrred.tenMul (K := ℂ) lam u) = F u := by
  first | exact @GlobalTheory.CoefIrred.vv_universal | exact GlobalTheory.CoefIrred.vv_universal | (intros; apply GlobalTheory.CoefIrred.vv_universal <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EasyInputs
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.EasyInputs

theorem smAll (D : D7) : SmAll D := fun V S M τ => by
  obtain ⟨w, hw, h0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (GlobalTheory.GardingVec.sm_ne_bot D V S M τ)
  exact ⟨⟨w, hw⟩, by simpa using h0⟩

theorem dimOK (D : D7) : DimOK D := fun i σ ρ => GlobalTheory.Mem.WeylDimPos.dimK_kapAt_Wc_pos D i σ ρ

theorem cartanOK (D : D7) : CartanOK D := by
  refine ⟨fun V S M _ τ => GlobalTheory.Chain.VacVec.cart_isCartanInv M τ, fun V hs hp τ => ?_⟩
  have h := GlobalTheory.RepsObj.gramAt_posDef hp hs τ
  exact ⟨by simp, by simp, by simpa using h⟩

theorem spOK (D : D7) : SpOK D := by
  refine ⟨fun τ => Or.inl ?_, fun τ => Or.inl (D.X'_posDef τ)⟩
  have hm : D.R.m - 1 ≤ D.R.m := Nat.sub_le _ _
  show (D.sp.Y (min (D.R.m - 1) D.R.m)).sig τ = ((D.sp.Y (min (D.R.m - 1) D.R.m)).rank, 0)
  rw [min_eq_left hm, D.Y_sigval _ hm τ, D.sp.Y_rank _ hm, sigYD]
  have := D.R.two_le_m
  have h1 : (D.R.m - (D.R.m - 1)) / 2 = 0 := by omega
  rw [h1, Nat.sub_zero]

theorem selfDualOK (D : D7) : SelfDualOK D := by
  rintro V β Λ N ⟨-, hd, hN, h1, h2⟩
  have hM0 : (N : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  have hL := (GlobalTheory.PlaceModel.isSelfDualC_latFrame V).1
  rw [← GlobalTheory.PlaceModel.coe_latFrame] at h1 h2
  refine ⟨⟨?_, ?_⟩, fun y => ?_⟩
  · let f : (Fin V.rank → D.host.E) →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E) :=
      (LinearMap.lsmul D.host.E (Fin V.rank → D.host.E) (N : D.host.E)⁻¹).restrictScalars (𝓞 D.host.E)
    refine (hL.fg.map f).of_le fun x hx => ⟨_, h2 x hx, ?_⟩
    change (N : D.host.E)⁻¹ • ((N : D.host.E) • x) = x
    rw [smul_smul, inv_mul_cancel₀ hM0, one_smul]
  · rw [eq_top_iff, ← hL.span_eq_top, Submodule.span_le]
    intro x hx
    have := Submodule.smul_mem _ (N : D.host.E)⁻¹
      (Submodule.subset_span (R := D.host.E) (s := (Λ : Set (Fin V.rank → D.host.E))) (h1 x hx))
    rwa [smul_smul, inv_mul_cancel₀ hM0, one_smul] at this
  · rw [← GlobalTheory.SDFrameLattice.mem_dualL_iff, hd]

open scoped Pointwise in

theorem petAll (D : D7) : PetAll D := by
  intro V μ 𝓕 hμ h𝓕 F hc hl h0 hi
  haveI : BorelSpace (GA D V) := ⟨rfl⟩
  haveI := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.isTopRing (F := D.host.F) (E := D.host.E)
  haveI : IsTopologicalGroup (GA D V) := inferInstanceAs (IsTopologicalGroup (HR (AF D.host.F) D.sp.cm.sig V.gram))
  haveI : Countable (GQ V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma _ _
  rw [setIntegral_pos_iff_support_of_nonneg_ae (Filter.Eventually.of_forall fun g => by positivity) hi]
  have hs : Function.support (fun g => ‖F g‖ ^ 2) = Function.support F := by
    ext g
    simp [Function.mem_support]
  rw [hs, pos_iff_ne_zero]
  intro hz
  have hinv : ∀ γ : GQ V, γ • Function.support F = Function.support F := fun γ => by
    ext g
    rw [Set.mem_smul_set_iff_inv_smul_mem, Function.mem_support, Function.mem_support]
    have : F (γ⁻¹ • g) = F g := hl _ (γ⁻¹).2 g
    rw [this]
  have hzero := h𝓕.measure_zero_of_invariant _ hinv hz
  exact (hc.isOpen_support.measure_pos μ (Function.support_nonempty_iff.2 h0)).ne' hzero

theorem easy_inputs : ∀ D : D7, CartanOK D ∧ SelfDualOK D ∧ SpOK D ∧ DimOK D ∧ PetAll D ∧ SmAll D := fun D =>
  ⟨cartanOK D, selfDualOK D, spOK D, dimOK D, petAll D, smAll D⟩

end GlobalTheory.Mem.EasyInputs
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqualRankSplittingCharsAdmissibleMulRight
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.WeilEqRank

variable {D : D7}

theorem equalRankSplittingCharsAdmissible_mul_right {V W : HSp D} {χ χ' ν : IdC D} (h : AdmE V W χ χ') (hν : IsHC D ν) (h0 : ResEta D ν 0) :
    AdmE V W χ (χ' * ν) :=
  ⟨h.1, h.2.1, (GlobalTheory.Mem.HeckeExp.hcSubgroup D).mul_mem (show χ' ∈ GlobalTheory.Mem.HeckeExp.hcSubgroup D from h.2.2.1)
    (show ν ∈ GlobalTheory.Mem.HeckeExp.hcSubgroup D from hν), h.2.2.2.1, resEta_mul h.2.2.2.2 h0⟩

theorem equalRankSplittingCharsAdmissible_mul_left {V W : HSp D} {χ χ' ν : IdC D} (h : AdmE V W χ χ') (hν : IsHC D ν) (h0 : ResEta D ν 0) :
    AdmE V W (χ * ν) χ' :=
  ⟨h.1, (GlobalTheory.Mem.HeckeExp.hcSubgroup D).mul_mem (show χ ∈ GlobalTheory.Mem.HeckeExp.hcSubgroup D from h.2.1)
    (show ν ∈ GlobalTheory.Mem.HeckeExp.hcSubgroup D from hν), h.2.2.1, resEta_mul h.2.2.2.1 h0, h.2.2.2.2⟩

theorem exists_weilFun_eqRank : ∀ D : D7, WeilEx D → WeilOnEqEx D → WeilTwEq D → ∀ ψ, IsStdChar D ψ (-1) →
    ∃ Wf : WeilFun D ψ, Wf.EqRank := by
  classical
  intro D h1 h2 h3 ψ hψ
  obtain ⟨W₀⟩ := h1 ψ hψ
  have key : ∀ (V W : HSp D) (χ χ' : IdC D), ∃ om : GA D V × GA D W →* Module.End ℂ (ThS ψ V W),
      (V.rank ≠ W.rank → om = W₀.om V W χ χ') ∧ (AdmE V W χ χ' → IsWeilOn ψ V W χ χ' om) := fun V W χ χ' => by
    by_cases h : AdmE V W χ χ'
    · obtain ⟨om, hom⟩ := h2 ψ hψ V W χ χ' h
      exact ⟨om, fun hne => absurd h.1 hne, fun _ => hom⟩
    · exact ⟨W₀.om V W χ χ', fun _ => rfl, fun k => absurd k h⟩
  choose om hne heq using key
  refine ⟨⟨om, fun V W χ χ' ha => ?_, fun V W χ χ' ha => ?_, fun V W χ χ' ha => ?_, fun V W χ χ' ha => ?_,
    fun V W χ χ' ha => ?_, fun V W χ χ' ν ha => ?_, fun V W χ χ' ν ha => ?_, fun V W χ χ' ha => ?_,
    fun V W χ χ' ha => ?_⟩, heq, fun V W χ χ' ν ha hν h0 => ?_, fun V W χ χ' ν ha hν h0 => ?_⟩
  · rw [hne V W χ χ' ha.1]; exact W₀.om_heis V W χ χ' ha
  · rw [hne V W χ χ' ha.1]; exact W₀.om_aut V W χ χ' ha
  · rw [hne V W χ χ' ha.1]; exact W₀.om_cont V W χ χ' ha
  · rw [hne V W χ χ' ha.1]; exact W₀.om_unit V W χ χ' ha
  · rw [hne V W χ χ' ha.1]; exact W₀.om_split V W χ χ' ha
  · rw [hne V W χ χ' ha.1, hne V W χ (χ' * ν) ha.1]; exact W₀.twW V W χ χ' ν ha
  · rw [hne V W χ χ' ha.1, hne V W (χ * ν) χ' ha.1]; exact W₀.twV V W χ χ' ν ha
  · rw [hne V W χ χ' ha.1, hne W V χ' χ ha.1.symm]; exact W₀.om_swap V W χ χ' ha
  · rw [hne V W χ χ' ha.1]; exact W₀.om_unr V W χ χ' ha
  · exact (h3 ψ hψ V W χ χ' ν ha hν h0 _ (heq V W χ χ' ha)).1 _ (heq V W χ (χ' * ν) (equalRankSplittingCharsAdmissible_mul_right ha hν h0))
  · exact (h3 ψ hψ V W χ χ' ν ha hν h0 _ (heq V W χ χ' ha)).2 _ (heq V W (χ * ν) χ' (equalRankSplittingCharsAdmissible_mul_left ha hν h0))

end GlobalTheory.Mem.WeilEqRank

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAlgHomEndomorphismOfSpanIntertwinersStatement
section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_algHom_endomorphism_of_span_intertwiners : ∀ (H W V : Type) [Group H] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] [AddCommGroup V] [Module ℂ V] (σ : Representation ℂ H W) (ρ : Representation ℂ H V), σ.IsIrreducible → (⨆ f : σ.IntertwiningMap ρ, LinearMap.range f.toLinearMap) = ⊤ → ∃ Φ : Module.End ℂ W →ₐ[ℂ] Module.End ℂ V, (∀ h, Φ (σ h) = ρ h) ∧ ∀ T : Module.End ℂ V, (∀ h, Commute T (ρ h)) → ∀ A, Commute T (Φ A) := by
  first | exact @GlobalTheory.FinPart.exists_algHom_end_of_span_intertwiners | exact GlobalTheory.FinPart.exists_algHom_end_of_span_intertwiners | (intros; apply GlobalTheory.FinPart.exists_algHom_end_of_span_intertwiners <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAlgHomFunctionFieldOfSpecializesGenericPoi
section
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle
open Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagBundle

theorem exists_algHom_of_specializes_genericPoint :
    ∀ (F : Type) [Field F] (Y : Var F) (K : Type) [Field K] [Algebra F K] (q : Sp K ⟶ Y.X),
      q (IsLocalRing.closedPoint K) ⤳ genericPoint Y.X → q ≫ Y.str = spMap (algebraMap F K) →
        ∃ ψ : Y.Fn →ₐ[F] K, q = spMap ψ.toRingHom ≫ (ratOf Y).pt := by
  intro F _ Y K _ _ q h hq
  let ψ₀ : Y.Fn →+* K := (Y.X.presheaf.stalkSpecializes h ≫ Scheme.stalkClosedPointTo (R := .of K) q).hom
  have e : spMap ψ₀ ≫ (ratOf Y).pt = q := by
    change Spec.map (CommRingCat.ofHom ψ₀) ≫ Y.X.fromSpecStalk (genericPoint Y.X) = q
    rw [CommRingCat.ofHom_hom, Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
    exact spMap_stalkClosedPointTo q
  have hc : ψ₀.comp (algebraMap F Y.Fn) = algebraMap F K := by
    have h1 : spMap (ψ₀.comp (algebraMap F Y.Fn)) = spMap (algebraMap F K) := by
      have hs := (ratOf Y).pt_s
      calc spMap (ψ₀.comp (algebraMap F Y.Fn)) = spMap ψ₀ ≫ spMap (algebraMap F Y.Fn) := by
            change Spec.map (CommRingCat.ofHom (ψ₀.comp (algebraMap F Y.Fn))) = _
            rw [CommRingCat.ofHom_comp, Spec.map_comp]
        _ = spMap ψ₀ ≫ ((ratOf Y).pt ≫ (ratOf Y).s) := by rw [hs]
        _ = (spMap ψ₀ ≫ (ratOf Y).pt) ≫ (ratOf Y).s := (Category.assoc _ _ _).symm
        _ = q ≫ Y.str := by
            change (spMap ψ₀ ≫ (ratOf Y).pt) ≫ Y.str = q ≫ Y.str
            rw [e]
            rfl
        _ = spMap (algebraMap F K) := hq
    have h2 := Spec.map_injective h1
    exact congrArg CommRingCat.Hom.hom h2
  refine ⟨{ ψ₀ with commutes' := fun a => congrArg (fun g : F →+* K => g a) hc }, ?_⟩
  exact e.symm

end GlobalTheory.FlagBundle
end
end

