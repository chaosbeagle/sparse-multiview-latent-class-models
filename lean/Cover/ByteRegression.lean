import Cover.ByteCodec
import Cover.Regression

namespace Cover.Regression
open Bytes

def evidenceSample : EvidenceCertificate 1 1 :=
  ⟨sampleCert, [0, 1, 2, 3, 5], [7, 11, 13]⟩

def byteChecks : List Bool := [
  decide (parseEvidenceByteArray 1 1 (serializeEvidenceByteArray evidenceSample) = some evidenceSample),
  decide (parseEvidenceBytes 1 1 [] = none),
  decide (parseEvidenceBytes 1 1 [255] = none),
  decide (parseEvidenceBytes 1 1 ((serializeEvidenceBytes evidenceSample).dropLast) = none),
  decide (parseEvidenceBytes 1 1 (serializeEvidenceBytes evidenceSample ++ [0]) = none),
  decide (parseEvidenceBytes 1 1 (serializeEvidenceBytes evidenceSample ++ [255]) = none),
  decide (parseEvidenceBytes 1 1 (encodeNat 1 ++ encodeNats [3]) = none),
  decide (parseEvidenceBytes 1 1 (encodeList encodeEvidenceToken [.refinements [1] [2], .base (.unknown 9)]) = none),
  decide (parseEvidenceBytes 1 1 (encodeNat 2 ++ encodeEvidenceToken (.refinements [1] [2])) = none),
  decide (decodeNat [1, 1, 1] = none),
  decide (decodeNat [1, 2, 0] = none)]

#eval do
  if byteChecks.all id then IO.println "All 11 raw-byte codec regressions passed."
  else throw (IO.userError "Raw-byte codec regression failed.")

end Cover.Regression
