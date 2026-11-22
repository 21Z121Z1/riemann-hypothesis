import Mathlib
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ThDistC
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.JetsAllOfColIn
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0008
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0094
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0102
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0135
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0123
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0081
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0010
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0002
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0012
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0321
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FundamentalDomainNeZero
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.FrameTransport
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryStabilizerAnisotropicVectorEquivComplemen
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0134
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0004

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ChThOkOfColIn
section
open NumberField IsDedekindDomain

noncomputable section

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.KerT
open GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree (degAt degNu)

namespace GlobalTheory.ChainTheta

section Step

variable {X : Fields} (A : Amb X) {a b : ℕ} (Sa SB : Finset (HeightOneSpectrum (𝓞 X.E))) (D : ℕ)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (mU : HeightOneSpectrum (𝓞 X.E) → X.Kˣ) (mI : SB → X.E → X.K)
  (lam : X.Tau → DomWeight a) (lam' : X.Tau → DomWeight b) (n : X.Tau → ℕ)

theorem thDistC_add_deg (hadd : A.IndAdd a b Sa D) (hsm : A.IndSmooth a b Sa D)
    (hrat : ∀ N N' c x, InRange Sa D c N N' x → ∀ m : DVar X.Tau a b →₀ ℕ, (∀ τ, (degAt m τ : ℤ) = degNu lam n τ) →
      ∃ k : X.K, A.σ₀ k = (A.chiF a b N N')⁻¹ * jetC A.cD (A.thInd Sa N N' c x) m)
    (N : Submodule (𝓞 X.E) (Sp X.E a)) (fr : Frs X.E a SB) (N' : Submodule (𝓞 X.E) (Sp X.E b)) (fr' : Frs X.E b SB)
    (c c' : ℕ) (x : HomE X.E a b) (hc : 0 < c) (hc' : 0 < c') (hR : InRange Sa D (c * c') N N' x) :
    thDistC A Sa SB D sel mU mI lam lam' n N fr N' fr' c x =
      latSum (mulLat c (homAt Sa N N')) (mulLat (c * c') (homAt Sa N N')) fun y =>
        thDistC A Sa SB D sel mU mI lam lam' n N fr N' fr' (c * c') (x + y) := by
  have := latFin X a b Sa N N' c c' hR.1 hR.2.1 hc hc'
  let _ := Fintype.ofFinite
    (↥(mulLat c (homAt Sa N N')) ⧸ (mulLat (c * c') (homAt Sa N N')).comap (mulLat c (homAt Sa N N')).subtype)
  set rep := fun z : ↥(mulLat c (homAt Sa N N')) ⧸ (mulLat (c * c') (homAt Sa N N')).comap (mulLat c (homAt Sa N N')).subtype =>
    ((Function.surjInv (Submodule.Quotient.mk_surjective
      ((mulLat (c * c') (homAt Sa N N')).comap (mulLat c (homAt Sa N N')).subtype)) z :
      ↥(mulLat c (homAt Sa N N'))) : HomE X.E a b) with hrep
  have hRz : ∀ z, InRange Sa D (c * c') N N' (x + rep z) := fun z => hR.add (Subtype.coe_prop _)
  have h1 : A.thInd Sa N N' c x = fun w => ∑ z, A.thInd Sa N N' (c * c') (x + rep z) w := by
    funext w
    rw [hadd N N' c c' x hc hc' hR w]
    unfold latSum
    rw [finsum_eq_sum_of_fintype]
  have hJ : jetOp lam lam' (A.jetK Sa N N' c x) n =
      jetOp lam lam' (fun m => ∑ z, A.jetK Sa N N' (c * c') (x + rep z) m) n := by
    refine GlobalTheory.JetIdentity.jetOp_congr lam lam' n _ _ fun m hm => ?_
    have h2 : derivAt0 (A.thInd Sa N N' c x) m = ∑ z, derivAt0 (A.thInd Sa N N' (c * c') (x + rep z)) m := by
      unfold derivAt0
      rw [h1, iteratedFDeriv_sum (fun z _ => hsm N N' (c * c') (x + rep z) (hRz z) _)]
      rw [Finset.sum_apply, _root_.sum_apply]
    choose k hk using fun z => hrat N N' (c * c') (x + rep z) (hRz z) m hm
    have h3 : (A.chiF a b N N')⁻¹ * jetC A.cD (A.thInd Sa N N' c x) m = A.σ₀ (∑ z, k z) := by
      rw [map_sum]
      simp only [hk]
      unfold jetC
      rw [h2, Finset.mul_sum, Finset.mul_sum]
    unfold Amb.jetK
    rw [h3, desc_map]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [← hk z, desc_map]
  unfold latSum
  rw [finsum_eq_sum_of_fintype]
  unfold thDistC
  rw [if_pos ⟨(Dvd.intro _ rfl).trans hR.2.2.2.1, hR.2.2.2.2⟩, hJ, Formalism.L2.Ker.jetOp_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun z _ => ?_
  exact (if_pos ⟨hR.2.2.2.1, mem_divLat_add D c _ hR.2.2.2.2 (Subtype.coe_prop _)⟩).symm

end Step

section Chain

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (A : Amb X) (u : Pr.Word)

theorem stepC_ok_deg (i : ℕ) (hi : i < R.m) (j : ℕ) (hT : 0 < Pr.T u) (hq : MuqTie Ch sel mu cst)
    (hL : A.LaHyp (R.N i) (R.N j) (Sall sel mu u)) (hE : A.ESmooth (R.N i) (R.N j))
    (hrat : ∀ N N' c x, InRange (Sall sel mu u) (cAof sel mu cst * cBof sel mu cst u) c N N' x →
      ∀ m : DVar X.Tau (R.N i) (R.N j) →₀ ℕ, (∀ τ, (degAt m τ : ℤ) = degNu (W.lamTrue u i) (nuLast W u i) τ) →
      ∃ k : X.K, A.σ₀ k = (A.chiF _ _ N N')⁻¹ * jetC A.cD (A.thInd (Sall sel mu u) N N' c x) m)
    (hR : RatStep W Ch sel mu cst A u i j) :
    ThDist.Ok (stepC W Ch sel mu cst A u i (W.lamTrue u j)) (Sall sel mu u) (cAof sel mu cst * cBof sel mu cst u)
      ((rhoVr X.emb (W.lamTrue u i)).comp (ufGL X.E (R.N i))) ((rhoVr X.emb (W.lamTrue u j)).comp (ufGL X.E (R.N j)))
      (rhoS Ch sel mu i) (rhoT Ch sel mu i) := by
  have hD := modulus_pos sel mu cst u hT
  unfold RatStep at hR
  rw [← stepC_eq_stepT W Ch sel mu cst hq A u i hi] at hR
  exact
    { cong := fun N fr N' fr' c x x' _ _ h => thDistC_cong A _ _ sel _ _ _ _ _ _ N fr N' fr' c x x' h
      add := fun N fr N' fr' c c' x hN hN' hc hc' hd hx =>
        thDistC_add_deg A _ _ _ sel _ _ _ _ _
          (indAdd_of A _ _ _ _ hD (latFin X _ _ _) (indTieD_of_la A _ _ _ _ hD hL)) (indSmooth_of A _ _ _ _ hE) hrat
          N fr N' fr' c c' x hc hc' ⟨hN, hN', Nat.mul_pos hc hc', hd, hx⟩
      equiv := thDistC_equiv A _ _ sel _ _ _ _ _ _ hD _ _ hR
      det := fun N fr N' fr' c x κ κ' _ _ =>
        thDistC_det A _ _ sel _ _ _ _ _ _ _ _ (muDetLaw_chain Ch sel mu cst i _) (muDetLaw_chain Ch sel mu cst i _)
          (unitInv_rho Ch sel mu i) N fr N' fr' c x κ κ' }

end Chain

theorem chTh_ok_of_hyp {Z : Dat} {H : D7} {s : Seam H Z.X} {cc : Ideal (𝓞 H.host.K)} {δ : ℂ} (B : Base H cc δ) {χ : TaylorLogMetric.IdE H → ℂ}
    {cD : H.what₂.Tau → ℂ} {sel : HeightOneSpectrum (𝓞 Z.X.F) → HeightOneSpectrum (𝓞 Z.X.E)} {S : Set ℕ}
    {mu : Tup Z.X.F Z.X.E Z.X.K S} {cst : LocCst Z.X (rowSG Z.Pr sel mu)} {u : Z.Pr.Word} {m2 : ℕ} (hm : Z.R.m = m2 + 2)
    (h : Hyp Z s cc δ χ cD sel S mu cst u) (hE : B.EqP χ) (hV : B.VecP χ) (hq : MuqTie Z.Ch sel mu cst)
    (hJ : ∀ i, i < Z.R.m → ∀ N N' c x, InRange (Sall sel mu u) (cAof sel mu cst * cBof sel mu cst u) c N N' x →
      ∀ m : DVar Z.X.Tau (Z.R.N i) (Z.R.N (i + 1)) →₀ ℕ, (∀ τ, (degAt m τ : ℤ) = degNu (Z.W.lamTrue u i) (nuLast Z.W u i) τ) →
      ∃ k : Z.X.K, (ambOf s B χ cD).σ₀ k = ((ambOf s B χ cD).chiF _ _ N N')⁻¹ *
        jetC (ambOf s B χ cD).cD ((ambOf s B χ cD).thInd (Sall sel mu u) N N' c x) m) :
    ChTh.Ok (Ch := Z.Ch) cst (chTh Z.W Z.Ch sel mu cst (ambOf s B χ cD) u m2) := by
  have bad := GlobalTheory.ThetaMove.BadPrimes.bad_primes Z.X Z.Pr sel S mu u h.ok.fields h.ok.primes h.isSel h.T_mem h.g_mem
  have key : ∀ i j, i < Z.R.m → j = i + 1 →
      ThDist.Ok (stepC Z.W Z.Ch sel mu cst (ambOf s B χ cD) u i (Z.W.lamTrue u j)) (Sall sel mu u)
        (cAof sel mu cst * cBof sel mu cst u) ((rhoVr Z.X.emb (Z.W.lamTrue u i)).comp (ufGL Z.X.E (Z.R.N i)))
        ((rhoVr Z.X.emb (Z.W.lamTrue u j)).comp (ufGL Z.X.E (Z.R.N j))) (rhoS Z.Ch sel mu i) (rhoT Z.Ch sel mu i) := by
    rintro i _ hi rfl
    obtain ⟨hL, hS⟩ := GlobalTheory.T.normalisedFamily_latticeHyp_and_smooth H Z.X s cc δ B χ cD (Z.R.N i) (Z.R.N (i + 1)) h.ok.fields h.ana.1 h.ana.2.2.1 h.ana.2.2.2.1 hV
      (GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree.even_N _ _) (GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree.even_N _ _)
    exact stepC_ok_deg Z.W Z.Ch sel mu cst _ u i hi (i + 1) (h.ok.primes.T_prime u).pos hq
      ⟨hL.1, hL.2.1, fun P hP => (bad P hP).1,
        fun P hP => GlobalTheory.PeriodIdealUnit.locP_AA_eq_one Z.X H s cc δ B χ cD P (bad P hP).2.1 (bad P hP).2.2.1 (h.cop P hP),
        hL.2.2.2.2⟩ hS (hJ i hi)
      (GlobalTheory.T.thetaStepDistribution_equivariant_rational Z H s cc δ B χ cD sel S mu cst u i hi h hE hV hq (hJ i hi))
  exact ⟨fun i hi => key i (i + 1) (by omega) rfl, key (m2 + 1) Z.R.m (by omega) hm⟩

open GlobalTheory.Mem GlobalTheory.Mem.Col2 in

theorem chTh_ok_of_colIn (B : GlobalTheory.Mem.Base) (C : Cols B) (W : RowsRest B C) (V : DivStage B C W) (S : SStage B C W) (N : NStage B C W)
    (G : GJStage B C) {X : PreX B.toPre} (I : ColIn B X) (h : I.Ok) (hJ : I.JetsIn)
    (hE : (I.J.toRec B C W V S N G).EqP I.chi) (hV : (I.J.toRec B C W V S N G).VecP I.chi)
    (a : I.ι) (u : B.Word) (m2 : ℕ) (hm : B.R.m = m2 + 2) :
    ChTh.Ok (Ch := I.Ch) (I.cst a) (chTh (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) (I.cst a) I.A u m2) := by
  have h1 := chTh_ok_of_hyp (Z := I.dat) (I.J.toRec B C W V S N G) hm (hyp_of_colIn B C W V S N G I h a u) hE hV
    (muqTie_of_ok _ _ _ _ _ (h.idx_ok a)) (by
      rw [← AmbIn.amb_eq_ambOf]
      intro i hi L L' c x hx m hd
      refine hJ.exists_eq hi hx fun τ => ?_
      rw [monoDeg_eq_sum]
      exact (hd τ).trans (GlobalTheory.MoveCompare.degNu_eq (Pr := B.primes X) B.wts u hi τ))
  rw [← AmbIn.amb_eq_ambOf] at h1
  exact h1

open GlobalTheory.Mem GlobalTheory.Mem.Col2 in

theorem chTh_ok_of_colIn' (B : GlobalTheory.Mem.Base) (C : Cols B) (W : RowsRest B C) (V : DivStage B C W) (S : SStage B C W) (N : NStage B C W)
    (G : GJStage B C) {X : PreX B.toPre} (I : ColIn B X) (h : I.Ok) (hJ : I.JetsIn)
    (hE : (I.J.toRec B C W V S N G).EqP I.chi) (hV : (I.J.toRec B C W V S N G).VecP I.chi) (a : I.ι) (u : B.Word) :
    ChTh.Ok (Ch := I.Ch) (I.cst a) (chTh (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) (I.cst a) I.A u (B.R.m - 2)) :=
  chTh_ok_of_colIn B C W V S N G I h hJ hE hV a u _ h.hm

end GlobalTheory.ChainTheta
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsAdelicUnitaryComplementRangeStabiliser
section
open NumberField MeasureTheory Matrix Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice GlobalTheory.IndefiniteRowSideFullHecke.InfiniteCoordinateUnfold GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryHaarMeasure GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeStabilizers GlobalTheory.Mem.Vol GlobalTheory.Mem.VolExists
open scoped ENNReal TensorProduct

noncomputable section

namespace GlobalTheory.StabiliserOfVector

open Formalism.UG (cT UJ)
open GlobalTheory.FrameStep

theorem exists_of_conj_fixed {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) {y : E} (hy : σ y = y) :
    ∃ a : F, algebraMap F E a = y := by
  obtain ⟨-, hE, h2, hτ⟩ := hCM
  have : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  let K : Submodule F E := LinearMap.ker (σ.toLinearMap - LinearMap.id)
  have hK : ∀ z, z ∈ K ↔ σ z = z := fun z => by simp [K, sub_eq_zero]
  have hne : K ≠ ⊤ := by
    intro h
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    refine IsTotallyComplex.complexEmbedding_not_isReal τ ?_
    rw [ComplexEmbedding.isReal_iff]
    ext z
    have hz : σ z = z := (hK z).1 (h ▸ Submodule.mem_top)
    have := hτ τ z
    rw [hz] at this
    exact this.symm
  have hlt := Submodule.finrank_lt hne
  have hle : Submodule.span F {(1 : E)} ≤ K := by
    rw [Submodule.span_singleton_le_iff_mem, hK, map_one]
  have heq : Submodule.span F {(1 : E)} = K := by
    refine Submodule.eq_of_le_of_finrank_le hle ?_
    rw [finrank_span_singleton one_ne_zero]
    omega
  have hmem : y ∈ Submodule.span F {(1 : E)} := heq ▸ (hK y).2 hy
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 hmem
  exact ⟨a, by rw [← ha, Algebra.algebraMap_eq_smul_one]⟩

theorem mem_ratPts_iff {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R]
    [Algebra F R] [Nontrivial R] (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (g : HA R σ J) :
    g ∈ ratPts R σ J ↔ ∃ k : Matrix (Fin M) (Fin M) E, k.map (inclR (F := F) R) =
      ((HA.mat R σ J g : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E)) := by
  constructor
  · rintro ⟨k, -, hk⟩
    exact ⟨k, congrArg (fun u : GL (Fin M) (R ⊗[F] E) => (u : Matrix (Fin M) (Fin M) (R ⊗[F] E))) hk⟩
  · rintro ⟨k, hk⟩
    have hinj : Function.Injective (inclR (F := F) (E := E) R) := (inclR (F := F) (E := E) R).injective
    have hdet : k.det ≠ 0 := by
      intro h0
      have hu : IsUnit (k.map (inclR (F := F) R)).det := by
        rw [hk]; exact (Matrix.isUnits_det_units _)
      have h1 := (inclR (F := F) (E := E) R).map_det k
      rw [h0, map_zero] at h1
      rw [RingHom.mapMatrix_apply] at h1
      rw [← h1] at hu
      exact not_isUnit_zero hu
    refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero k hdet, ?_, Units.ext hk⟩
    show cT (σ : E →+* E) k * J * k = J
    apply Matrix.map_injective hinj
    have hg : cT (sigR R σ) (HA.mat R σ J g : Matrix (Fin M) (Fin M) (R ⊗[F] E)) * JR R J *
      (HA.mat R σ J g : Matrix (Fin M) (Fin M) (R ⊗[F] E)) = JR R J := g.2
    rw [← hk, cT_map, JR, ← Matrix.map_mul, ← Matrix.map_mul] at hg
    exact hg

theorem exists_hom_range_stabiliser : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M M' : ℕ) (J : Matrix (Fin M) (Fin M) E) (J' : Matrix (Fin M') (Fin M') E) (B : Matrix (Fin M) (Fin M') E) (x : Fin 1 → Fin M → E), M' + 1 = M → IsHermND σ J → IsHermND σ J' → Formalism.UG.cT (σ : E →+* E) B * J * B = J' → (∀ j, hE σ J (x 0) (fun i => B i j) = 0) → hE σ J (x 0) (x 0) ≠ 0 → ∃ φ : HA (AF F) σ J' →* HA (AF F) σ J, Continuous φ ∧ Function.Injective φ ∧ φ.range = Hstab (AF F) σ J x ∧ (∀ g, FrameRel J J' B (φ g) g) ∧ ∀ g, φ g ∈ ratPts (AF F) σ J ↔ g ∈ ratPts (AF F) σ J' := by
  intro F E _ _ _ _ _ σ hCM M M' J J' B x hM hJ hJ' hBB hxB hxx
  subst hM
  have hσ : ∀ y, σ (σ y) = y := by
    intro y
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    apply τ.injective
    rw [hCM.2.2.2, hCM.2.2.2, star_star]
  have hfix : σ (hE σ J (x 0) (x 0)) = hE σ J (x 0) (x 0) := by
    simp only [hE, Formalism.UG.hform, map_sum, map_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hJ.1 i j]
    show σ (σ (x 0 j)) * J i j * σ (x 0 i) = σ (x 0 i) * J i j * x 0 j
    rw [hσ]; ring
  obtain ⟨a, ha⟩ := exists_of_conj_fixed σ hCM hfix
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact hxx (by rw [← ha, map_zero])
  have h : GlobalTheory.GaugeEx.StepData σ J x a B J' := ⟨hJ, ha0, ha.symm, hxB, hBB.symm, hJ'⟩
  obtain ⟨-, L₁, L, c, hL, h11, h21, h22, hsum, hXB, hBX⟩ := exists_dual σ hσ h
  have : Nontrivial (AF F) := inferInstanceAs (Nontrivial (InfiniteAdeleRing F × _))
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.isTopRing (F := F) (E := E)
  set X : Matrix (Fin (M' + 1)) (Fin 1) E := (Matrix.of x).transpose with hXdef
  set ι : E →+* AF F ⊗[F] E := inclR (AF F) with hι
  have hone : ∀ k : ℕ, (1 : Matrix (Fin k) (Fin k) E).map ι = 1 := fun k =>
    Matrix.map_one _ (map_zero ι) (map_one ι)
  have hzero : ∀ k l : ℕ, (0 : Matrix (Fin k) (Fin l) E).map ι = 0 := fun k l =>
    Matrix.map_zero _ (map_zero ι)
  have h22' : L.map ι * B.map ι = 1 := by rw [← Matrix.map_mul, h22, hone]
  have hsum' : X.map ι * L₁.map ι + B.map ι * L.map ι = 1 := by
    rw [← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_add _ (map_add ι), hsum, hone]
  have hS : ∀ g : HA (AF F) σ J, g ∈ Hstab (AF F) σ J x ↔
      ((HA.mat (AF F) σ J g : GL (Fin (M' + 1)) (AF F ⊗[F] E)) :
        Matrix (Fin (M' + 1)) (Fin (M' + 1)) (AF F ⊗[F] E)) * X.map ι = X.map ι := by
    intro g
    refine MulAction.mem_stabilizer_iff.trans ⟨fun hg => ?_, fun hg => ?_⟩
    · ext i j
      exact congrFun (congrFun hg j) i
    · funext j i
      exact congrFun (congrFun hg i) j
  obtain ⟨e, he⟩ : ∃ e : Hstab (AF F) σ J x ≃* HA (AF F) σ J',
      ∀ g : Hstab (AF F) σ J x, FrameRel J J' B (g : HA (AF F) σ J) (e g) :=
    exists_equiv (sigR (AF F) σ) (JR (AF F) J) (JR (AF F) J') (X.map ι) (B.map ι) (L₁.map ι)
      (L.map ι) (c.map ι)
      (by rw [hL, Matrix.map_mul, Matrix.map_mul, cT_map]; rfl)
      (by rw [← Matrix.map_mul, h11, hone]) (by rw [← Matrix.map_mul, h21, hzero]) h22' hsum'
      (by rw [cT_map, JR, ← Matrix.map_mul, ← Matrix.map_mul, hXB, hzero])
      (by rw [cT_map, JR, ← Matrix.map_mul, ← Matrix.map_mul, hBX, hzero])
      (by rw [cT_map, JR, ← Matrix.map_mul, ← Matrix.map_mul, hBB]; rfl)
      (Hstab (AF F) σ J x) hS
  let φ : HA (AF F) σ J' →* HA (AF F) σ J :=
    (Hstab (AF F) σ J x).subtype.comp e.symm.toMonoidHom
  have hφ : ∀ g, φ g = (e.symm g : HA (AF F) σ J) := fun g => rfl
  have hrel : ∀ g, FrameRel J J' B (φ g) g := by
    intro g
    have := he (e.symm g)
    rwa [MulEquiv.apply_symm_apply] at this
  have hfor : ∀ g, ((HA.mat (AF F) σ J' g : GL (Fin M') (AF F ⊗[F] E)) :
      Matrix (Fin M') (Fin M') (AF F ⊗[F] E)) =
        L.map ι * ((HA.mat (AF F) σ J (φ g) : GL (Fin (M' + 1)) (AF F ⊗[F] E)) :
        Matrix (Fin (M' + 1)) (Fin (M' + 1)) (AF F ⊗[F] E)) * B.map ι := by
    intro g
    have hr := hrel g
    rw [FrameRel, ← hι] at hr
    rw [Matrix.mul_assoc]
    erw [hr, ← Matrix.mul_assoc, h22', Matrix.one_mul]
  have hback : ∀ g, ((HA.mat (AF F) σ J (φ g) : GL (Fin (M' + 1)) (AF F ⊗[F] E)) :
        Matrix (Fin (M' + 1)) (Fin (M' + 1)) (AF F ⊗[F] E)) =
        X.map ι * L₁.map ι +
          B.map ι * ((HA.mat (AF F) σ J' g : GL (Fin M') (AF F ⊗[F] E)) :
            Matrix (Fin M') (Fin M') (AF F ⊗[F] E)) * L.map ι := by
    intro g
    have hr := hrel g
    rw [FrameRel, ← hι] at hr
    have h3 := congrArg (((HA.mat (AF F) σ J (φ g) : GL (Fin (M' + 1)) (AF F ⊗[F] E)) :
      Matrix (Fin (M' + 1)) (Fin (M' + 1)) (AF F ⊗[F] E)) * ·) hsum'
    simp only [Matrix.mul_add, ← Matrix.mul_assoc, Matrix.mul_one] at h3
    rw [(hS (φ g)).1 (e.symm g).2] at h3
    erw [hr] at h3
    exact h3.symm
  have cm : Continuous fun g : HA (AF F) σ J' => HA.mat (AF F) σ J' g := continuous_subtype_val
  have cφ : ∀ f : HA (AF F) σ J' → HA (AF F) σ J',
      (Continuous fun g => ((HA.mat (AF F) σ J' (f g) : GL (Fin M') (AF F ⊗[F] E)) :
            Matrix (Fin M') (Fin M') (AF F ⊗[F] E))) →
      Continuous fun g => ((HA.mat (AF F) σ J (φ (f g)) : GL (Fin (M' + 1)) (AF F ⊗[F] E)) :
        Matrix (Fin (M' + 1)) (Fin (M' + 1)) (AF F ⊗[F] E)) := by
    intro f hf
    simp only [hback]
    exact continuous_const.add ((continuous_const.matrix_mul hf).matrix_mul continuous_const)
  refine ⟨φ, ?_, Subtype.val_injective.comp e.symm.injective, ?_, hrel, fun g => ?_⟩
  · refine continuous_into (AF F) σ J _ (cφ id (Units.continuous_val.comp cm)) ?_
    simp only [← map_inv]
    exact cφ (fun g => g⁻¹) (Units.continuous_coe_inv.comp cm)
  · ext h
    constructor
    · rintro ⟨g, rfl⟩
      exact (e.symm g).2
    · intro hh
      exact ⟨e ⟨h, hh⟩, by rw [hφ, MulEquiv.symm_apply_apply]⟩
  · rw [mem_ratPts_iff, mem_ratPts_iff]
    constructor
    · rintro ⟨k, hk⟩
      exact ⟨L * k * B, by rw [hfor, ← hk, Matrix.map_mul, Matrix.map_mul]⟩
    · rintro ⟨k, hk⟩
      exact ⟨X * L₁ + B * k * L, by
        rw [hback, ← hk, Matrix.map_add _ (map_add _), Matrix.map_mul, Matrix.map_mul,
          Matrix.map_mul]⟩

end GlobalTheory.StabiliserOfVector
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsComplementFrameCompatibleStabilizerEmbeddi
section
open NumberField MeasureTheory Matrix Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice GlobalTheory.IndefiniteRowSideFullHecke.InfiniteCoordinateUnfold GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryHaarMeasure GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeStabilizers GlobalTheory.Mem.Vol GlobalTheory.Mem.VolExists
open scoped ENNReal TensorProduct

namespace GlobalTheory.StabFrameCompat

theorem exists_factor {P Q P' Q' : ℕ} (hc : P' + Q' + 1 = P + Q) {x : Fin P ⊕ Fin Q → ℂ}
    (hx : star x ⬝ᵥ Formalism.UG.Jpq P Q *ᵥ x ≠ 0)
    {C : Matrix (Fin P ⊕ Fin Q) (Fin P' ⊕ Fin Q') ℂ}
    (h1 : Cᴴ * Formalism.UG.Jpq P Q * C = Formalism.UG.Jpq P' Q')
    (h2 : (Cᴴ * Formalism.UG.Jpq P Q) *ᵥ x = 0) {m : Type} [Fintype m]
    (Y : Matrix (Fin P ⊕ Fin Q) m ℂ) (hY : (Yᴴ * Formalism.UG.Jpq P Q) *ᵥ x = 0) :
    ∃ U : Matrix (Fin P' ⊕ Fin Q') m ℂ, Y = C * U := by
  obtain ⟨N, -, -, hN, -⟩ := GlobalTheory.UnfoldingCompare.exists_frame_inv hc hx h1 h2
  set X : Matrix (Fin P ⊕ Fin Q) Unit ℂ := replicateCol Unit x with hX
  have e : Y = C * (N * Y).toRows₁ + X * (N * Y).toRows₂ := by
    rw [← fromCols_mul_fromRows, fromRows_toRows, ← Matrix.mul_assoc, hN, Matrix.one_mul]
  set U := (N * Y).toRows₁
  set V := (N * Y).toRows₂
  refine ⟨U, ?_⟩
  have hV : V = 0 := by
    have h3 : (Yᴴ * Formalism.UG.Jpq P Q) *ᵥ x
        = Uᴴ *ᵥ ((Cᴴ * Formalism.UG.Jpq P Q) *ᵥ x) + Vᴴ *ᵥ ((Xᴴ * Formalism.UG.Jpq P Q) *ᵥ x) := by
      conv_lhs => rw [e]
      rw [conjTranspose_add, conjTranspose_mul, conjTranspose_mul, Matrix.add_mul, add_mulVec,
        Matrix.mul_assoc, Matrix.mul_assoc, ← mulVec_mulVec, ← mulVec_mulVec x Vᴴ]
    rw [hY, h2, mulVec_zero, zero_add] at h3
    have h4 : ((Xᴴ * Formalism.UG.Jpq P Q) *ᵥ x) () = star x ⬝ᵥ Formalism.UG.Jpq P Q *ᵥ x := by
      rw [← mulVec_mulVec]
      rfl
    ext u i
    have h5 := congrFun h3 i
    rw [Pi.zero_apply, mulVec, dotProduct, Fintype.sum_unique] at h5
    have h6 : star (V () i) * (star x ⬝ᵥ Formalism.UG.Jpq P Q *ᵥ x) = 0 := by
      rw [← h4]; exact h5.symm
    rcases mul_eq_zero.1 h6 with h | h
    · simpa using h
    · exact absurd h hx
  rw [hV, Matrix.mul_zero, add_zero] at e
  exact e

theorem exists_compatible_frame : ∀ (P Q P' Q' M M' : ℕ), P' + Q' + 1 = P + Q → M' = P' + Q' → ∀ (G : Matrix (Fin M) (Fin M) ℂ) (G' : Matrix (Fin M') (Fin M') ℂ) (B : Matrix (Fin M) (Fin M') ℂ) (x : Fin M → ℂ) (A : Matrix (Fin P ⊕ Fin Q) (Fin M) ℂ), Aᴴ * Formalism.UG.Jpq P Q * A = G → Bᴴ * G * B = G' → G'.det ≠ 0 → (Bᴴ * G) *ᵥ x = 0 → star (A *ᵥ x) ⬝ᵥ Formalism.UG.Jpq P Q *ᵥ (A *ᵥ x) ≠ 0 → ∀ j : UpqT P' Q' →* UpqT P Q, IsStabEmb (A *ᵥ x) j → ∃ A' : Matrix (Fin P' ⊕ Fin Q') (Fin M') ℂ, A'ᴴ * Formalism.UG.Jpq P' Q' * A' = G' ∧ ∀ (g : Matrix (Fin M) (Fin M) ℂ) (g' : Matrix (Fin M') (Fin M') ℂ) (t : UpqT P Q) (t' : UpqT P' Q'), g *ᵥ x = x → g * B = B * g' → UpqT.mat t * A = A * g → UpqT.mat t' * A' = A' * g' → t = j t' := by
  intro P Q P' Q' M M' hc hM G G' B x A hA hB hdet hBx hx j hj
  obtain ⟨C, h1, h2, h3⟩ := hj
  have hY : ((A * B)ᴴ * Formalism.UG.Jpq P Q) *ᵥ (A *ᵥ x) = 0 := by
    rw [mulVec_mulVec, conjTranspose_mul, ← hBx, ← hA]
    simp only [Matrix.mul_assoc]
  obtain ⟨A', hA'⟩ := exists_factor hc hx h1 h2 (A * B) hY
  have hG : A'ᴴ * Formalism.UG.Jpq P' Q' * A' = G' := by
    have : (C * A')ᴴ * Formalism.UG.Jpq P Q * (C * A') = G' := by
      rw [← hA', ← hB, ← hA, conjTranspose_mul]
      simp only [Matrix.mul_assoc]
    rw [← this, ← h1, conjTranspose_mul]
    simp only [Matrix.mul_assoc]
  refine ⟨A', hG, ?_⟩
  intro g g' t t' hg hgB ht ht'
  have hl : (G'⁻¹ * A'ᴴ * Formalism.UG.Jpq P' Q') * A' = 1 := by
    have := Matrix.nonsing_inv_mul G' (Ne.isUnit hdet)
    rw [← this]
    conv_rhs => arg 2; rw [← hG]
    simp only [Matrix.mul_assoc]
  have e : Fin M' ≃ Fin P' ⊕ Fin Q' := (finCongr hM).trans finSumFinEquiv.symm
  have hr : A' * (G'⁻¹ * A'ᴴ * Formalism.UG.Jpq P' Q') = 1 :=
    (Matrix.mul_eq_one_comm_of_equiv e).1 hl
  refine GlobalTheory.UnfoldingCompare.eq_of_frame hc hx h1 h2 ?_ ?_
  · have k : UpqT.mat t * C * A' = UpqT.mat (j t') * C * A' := by
      rw [(h3 t').2, Matrix.mul_assoc, Matrix.mul_assoc, ← hA', ht', ← Matrix.mul_assoc,
        ← Matrix.mul_assoc, ← hA', ht, Matrix.mul_assoc, hgB, Matrix.mul_assoc]
    calc UpqT.mat t * C = UpqT.mat t * C * (A' * (G'⁻¹ * A'ᴴ * Formalism.UG.Jpq P' Q')) := by
          rw [hr, Matrix.mul_one]
      _ = UpqT.mat (j t') * C * (A' * (G'⁻¹ * A'ᴴ * Formalism.UG.Jpq P' Q')) := by
          rw [← Matrix.mul_assoc _ A', k, Matrix.mul_assoc _ A']
      _ = _ := by rw [hr, Matrix.mul_one]
  · rw [(h3 t').1, mulVec_mulVec, ht, ← mulVec_mulVec, hg]

end GlobalTheory.StabFrameCompat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsUniqueIsStandardAdeleCharUnramifiedCMBaseStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.LocalDualIndex
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsUnique_isStandardAdeleChar_unramifiedCM_base : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E] (σ : E →ₐ[F] E), IsCMExt F E σ → (∀ x : E, star x = σ x) → Formalism.HermitianLatticesTheory.IsCMUnram E → ∃! ψ₀ : AddChar (AF F) ℂ, IsStdChar F ψ₀ := by
  first | exact @GlobalTheory.StdCharUnique.existsUnique_isStdChar_cm | exact GlobalTheory.StdCharUnique.existsUnique_isStdChar_cm | (intros; apply GlobalTheory.StdCharUnique.existsUnique_isStdChar_cm <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FiniteAdelicUnitaryGroupStabilizersUnimodularStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryHaarMeasure
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteAdelicUnitaryGroup_stabilizers_unimodular : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → UnimodularOver (Af F) σ J := by
  first | exact @GlobalTheory.FiniteAdelicUnimod.unimodularOver_finiteAdele | exact GlobalTheory.FiniteAdelicUnimod.unimodularOver_finiteAdele | (intros; apply GlobalTheory.FiniteAdelicUnimod.unimodularOver_finiteAdele <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HermitianFormAndSelfDualLatticeInFrameCoords
section
open NumberField MeasureTheory Matrix Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice GlobalTheory.IndefiniteRowSideFullHecke.InfiniteCoordinateUnfold GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryHaarMeasure GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeStabilizers GlobalTheory.Mem.Vol GlobalTheory.Mem.VolExists
open scoped ENNReal TensorProduct

namespace GlobalTheory.FrameDict

theorem form_coords {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E]
    [Algebra F E] (cm : CMData F E) (W : Formalism.BasicNotions.HSpace E) (x y : Fin W.rank → E) :
    hE cm.sig W.gram x y = W.hT (∑ i, x i • W.frame i) (∑ i, y i • W.frame i) := by
  have hs : ∀ a : E, (cm.sig : E →+* E) a = star a := fun _ => rfl
  simp only [hE, Formalism.UG.hform, map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ, map_smul,
    LinearMap.smul_apply, smul_eq_mul, Formalism.BasicNotions.HSpace.gram, hs,
    Finset.mul_sum, starRingEnd_apply, RingHom.id_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem mem_one_iff {E : Type} [Field E] [NumberField E] (z : E) :
    z ∈ (1 : Submodule (𝓞 E) E) ↔ IsIntegral ℤ z := by
  rw [Submodule.mem_one]
  constructor
  · rintro ⟨y, rfl⟩
    exact y.2
  · intro h
    exact ⟨⟨z, h⟩, rfl⟩

theorem dict : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E) (W : HSpace E), (∀ a b : W.V, hE cm.sig W.gram (fun i => W.frame.repr a i) (fun i => W.frame.repr b i) = W.hT a b) ∧ ∃ L : Submodule (𝓞 E) (Fin W.rank → E), IsSelfDualLat cm.sig W.gram L ∧ (L : Set (Fin W.rank → E)) = latC W := by
  intro F E _ _ _ _ _ _ cm W
  refine ⟨fun a b => ?_, ?_⟩
  · rw [form_coords, W.frame.sum_repr, W.frame.sum_repr]
  obtain ⟨L, hfg, hsp, hL⟩ := exists_lattice W
  refine ⟨L, ⟨hfg, hsp, fun y => ?_⟩, hL⟩
  have hmem : ∀ x : Fin W.rank → E, x ∈ L ↔ ∑ i, x i • W.frame i ∈ W.L0 := fun x => by
    rw [← SetLike.mem_coe, hL]; rfl
  have hu : ∀ v : W.V, (∀ u ∈ W.L0, W.hT u v ∈ (1 : Submodule (𝓞 E) E)) ↔ v ∈ W.L0 := fun v => by
    have h : Formalism.HermitianLatticesTheory.dual W.hT W.L0 = W.L0 := W.baseLattice_isUnimodular
    conv_rhs => rw [← h]
    simp [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf]
  rw [hmem, ← hu]
  constructor
  · intro h x hx
    rw [form_coords, ← mem_one_iff]
    exact h _ ((hmem x).1 hx)
  · intro h u hu'
    have := h (fun i => W.frame.repr u i) (by rw [hmem, W.frame.sum_repr]; exact hu')
    rw [form_coords, W.frame.sum_repr, ← mem_one_iff] at this
    exact this

end GlobalTheory.FrameDict
end

