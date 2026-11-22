import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.IdeleNormCharacters.Bundle0001
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.IdeleNormCharacters.Bundle0002
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.IdeleNormCharacters.TypVal
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.IdeleNormCharacters.ChrPairsPf

namespace UpperTheory.Gal.TP.Chr

theorem chrEx_holds : ChrEx := chrEx muEmb readEx readLoc readRes readExp absFacts (typProd typVal) expInj

theorem chrPairs_holds : UpperTheory.Gal.TP.Sub.ChrPairs := chrPairs chrEx_holds typVal

end UpperTheory.Gal.TP.Chr
