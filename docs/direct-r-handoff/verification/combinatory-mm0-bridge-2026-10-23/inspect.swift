import Foundation
import AppKit
import PDFKit

let pdfPath = CommandLine.arguments[1]
let out = CommandLine.arguments[2]
let sourceDir = URL(fileURLWithPath: pdfPath).deletingLastPathComponent()
guard let doc = PDFDocument(url: URL(fileURLWithPath: pdfPath)) else {
    fatalError("Unreadable PDF")
}
let pages = (0..<doc.pageCount).map { doc.page(at: $0)! }
let text = pages.map { $0.string ?? "" }.joined(separator: "\n")
for needle in ["Hilbert", "modus ponens", "Bunder", "QIIRT", "tyOf", "TyExact",
               "Completeness of the literal catalogue", "Metamath Zero",
               "h_universe", "h_apply", "h_convert", "coreS", "sortK2l", "sortS",
               "Rank-typed BCKW arithmetic", "7n + 2", "RedexBound",
               "Finite carriers", "Consistency-sensitive ground reduction", "NonLamNf",
               "typed-normal-bound", "applyWithinFinite", "applyTypedWithin",
               "FiniteWalk", "Maybe", "TypedResult", "Church compilation at explicit ranks",
               "Compiling reduction passes", "Fragment interpretations and internal consistency",
               "passProgram", "applicationProgram", "reductionProgram",
               "applyReductionProgram", "Pakhomov", "1907.00877v2",
               "Future work", "Quadratic type checking for objective type theory",
               "2102.00905", "Contextual certificate soundness", "ModelInput", "InputAccepted",
               "model-soundness", "Void-empty", "accepted-Void-rejected",
               "Exact finite ground fragments", "signed diagram",
               "query_program", "formula_program", "denial_program",
               "Checking all valuations in a fixed finite candidate", "check_candidate",
               "Explicit size/depth-guarded quantified fragments",
               "Literal MM0 adequacy and finite models",
               "Consistent finite models of all guarded MM0 schemas",
               "Proof height is a separate parameter", "Composition adds path budgets"] {
    guard text.lowercased().contains(needle.lowercased()) else {
        fatalError("Missing required content: \(needle)")
    }
}
guard let appendix = pages.firstIndex(where: {
    ($0.string ?? "").contains("Complete MM0 source")
}) else { fatalError("Missing MM0 appendix") }
guard (1...3).contains(doc.pageCount - appendix) else {
    fatalError("Full MM0 appendix exceeds three pages")
}
let appendixText = pages[appendix...].map { $0.string ?? "" }.joined(separator: "\n")
guard appendixText.contains("strict sort nat"), appendixText.contains("ENDHILBERT") else {
    fatalError("Incomplete source listing")
}
let bodyText = pages[..<appendix].map { $0.string ?? "" }.joined(separator: "\n")
guard bodyText.contains("5.2 A Metamath Zero specification"),
      bodyText.contains("h_apply"), bodyText.contains("h_type") else {
    fatalError("Missing Hilbert-section source excerpt")
}
guard bodyText.contains("RankedTy"),
      !bodyText.contains("AnyTy") else { fatalError("Stale Agda notation") }
guard !bodyText.contains("\\texttt{") else {
    fatalError("Unprocessed LaTeX text command in Markdown prose")
}
for rawMath in ["$$", "\\setminus", "\\cup", "\\Longleftrightarrow"] {
    guard !bodyText.contains(rawMath) else {
        fatalError("Unprocessed display mathematics: \(rawMath)")
    }
}
guard !bodyText.contains("Why substitutions retain both context indices") else {
    fatalError("Removed subsection is still present")
}
for forbidden in ["Duplication and an affine generator", "Duplication/affine numeral",
                  "The independent four-family core", "49n", "BJ output"] {
    guard !bodyText.contains(forbidden) else { fatalError("Stale content: \(forbidden)") }
}
guard bodyText.contains("↑↑"), bodyText.contains("BCKW") else {
    fatalError("Missing Knuth notation or basis")
}
let orderedHeadings = [
    "The calculus and its logical reading", "Rank-typed BCKW arithmetic",
    "Why a fixed finite typed basis is impossible",
    "Dependent logical schemes", "A complete Hilbert presentation",
    "The literal catalogue and its completeness boundary", "A Metamath Zero specification",
    "A first-order algebraic presentation as QIIRT",
    "Elementary normalization and finite syntax carriers",
    "Inductive-inductive-recursive normal representatives",
    "Total typed apply-and-normalize",
    "Church compilation at explicit ranks", "Compiling reduction passes",
    "Graded fragment soundness", "Contextual certificate soundness",
    "Fragment interpretations and internal consistency",
    "A locally finitely satisfiable target",
    "Explicit size/depth-guarded quantified fragments", "The exact typed expansion quotient",
    "Future work", "References"]
var previous = bodyText.startIndex
for heading in orderedHeadings {
    guard let range = bodyText.range(of: heading, range: previous..<bodyText.endIndex) else {
        fatalError("Missing or out-of-order heading: \(heading)")
    }
    previous = range.upperBound
}
for name in ["BCKW.agda", "Exact.agda", "NormalForms.agda", "TypedNormalFibres.agda",
             "FiniteApplication.agda", "FiniteTrace.agda", "TypedApplication.agda",
             "ChurchFinite.agda", "FiniteMachine.agda", "NativeSubstitution.agda",
             "NativeConfluence.agda", "NativePreservation.agda", "NativeDescent.agda",
             "NativeRankPreservation.agda", "NativeNormalization.agda",
             "FragmentEmbeddings.agda", "FragmentApplication.agda"] {
    guard FileManager.default.fileExists(atPath:
        sourceDir.appendingPathComponent("agda/" + name).path) else {
        fatalError("Missing checked-source link target: \(name)")
    }
}
let urls = pages.flatMap { $0.annotations.compactMap { $0.url } }
let remote = pages.flatMap { $0.annotations.compactMap { ($0.action as? PDFActionRemoteGoTo)?.url } }
let links = urls + remote
let sourceLinks = links.filter { $0.pathExtension == "v" }
guard sourceLinks.count == 56 else { fatalError("Missing formalization badges") }
for link in sourceLinks {
    guard FileManager.default.fileExists(atPath:
        sourceDir.appendingPathComponent(link.lastPathComponent).path) else {
        fatalError("Badge source missing: \(link)")
    }
}
for name in ["GroundHornConsistency.v", "FiniteHorn.v", "HilbertGrounding.v",
             "NativeCanonicity.v", "FiniteModelBoundary.v", "FiniteHornChurch.v",
             "HilbertFiniteModels.v", "FiniteUniversalHorn.v",
             "FiniteNativeModelBoundary.v", "FiniteAlgebraSearch.v",
             "FiniteOperationAlgebras.v", "MM0FiniteSignature.v",
             "MM0FiniteAxioms.v", "MM0FiniteSearch.v", "MM0ProjectionModel.v",
             "FiniteModelRealization.v", "FiniteModelSoundness.v",
             "MM0SyntaxSoundness.v", "MM0InternalSoundness.v",
             "GuardedFiniteCarriers.v", "GuardedHornFragments.v",
             "GuardedHilbertModels.v", "GuardedBetaGraphs.v",
             "GuardedHilbertTables.v", "GuardedHilbertCoverage.v", "MM0GuardedQuantification.v",
             "MM0NativeSyntax.v", "MM0ComputationalAdequacy.v", "MM0NativeReduction.v",
             "MM0CatalogueAdequacy.v", "MM0CatalogueRealization.v",
             "MM0GuardedSyntaxAlgebra.v", "MM0GuardedReflection.v", "MM0HilbertAdequacy.v"] {
    guard sourceLinks.contains(where: { $0.lastPathComponent == name }) else {
        fatalError("Missing constrained-model proof badge: \(name)")
    }
}
let agdaLinks = links.filter { $0.pathExtension == "agda" }
for link in agdaLinks {
    guard FileManager.default.fileExists(atPath:
        sourceDir.appendingPathComponent("agda/" + link.lastPathComponent).path) else {
        fatalError("Agda source target missing: \(link)")
    }
}
let agdaBadges = pages.flatMap { page in
    page.annotations.filter { annotation in
        let url = annotation.url ?? (annotation.action as? PDFActionRemoteGoTo)?.url
        return url?.pathExtension == "agda" &&
            (page.selection(for: annotation.bounds)?.string ?? "").contains("agda (proof)")
    }
}
guard agdaBadges.count == 27 else { fatalError("Missing Agda proof badges") }
for name in ["NormalForms.agda", "FiniteCarriers.agda", "FiniteBounds.agda",
             "TypedNormalFibres.agda", "RawSizeBounds.agda", "BoundedTrace.agda",
             "FiniteTrace.agda", "FiniteApplication.agda", "TypedApplication.agda",
             "ChurchFinite.agda", "FiniteMachine.agda", "NativeSubstitution.agda",
             "NativeConfluence.agda", "NativePreservation.agda", "NativeDescent.agda",
             "NativeRankPreservation.agda", "NativeNormalization.agda",
             "FragmentEmbeddings.agda", "FragmentApplication.agda",
             "FragmentMachineSoundness.agda", "FragmentAlphabet.agda",
             "NativeCertificates.agda", "CertificateContexts.agda",
             "ContextualNormalization.agda", "FragmentPackages.agda",
             "FragmentModelSoundness.agda", "NativeCanonicity.agda"] {
    guard agdaLinks.contains(where: { $0.lastPathComponent == name }),
          FileManager.default.fileExists(atPath:
            sourceDir.appendingPathComponent("agda/" + name).path) else {
        fatalError("Missing Agda proof link/target: \(name)")
    }
}
for needle in ["10.2168/LMCS-4(1:1)2008", "tt-qiirt_cpp2026.pdf",
               "10.1007/978-3-030-53518-6_5", "/mm0.md", "CombinatoryPTS-rk.mm0",
               "CombinatoryPTS-rk-examples.mm1", "agda/BCKW.agda",
               "agda/Exact.agda", "10.1017/S0956796897002888", "1907.00877v2",
               "ChurchFinite.v", "agda/ChurchFinite.agda", "agda/FiniteMachine.agda",
               "2102.00905", "10.1016/S0304-3975(02)00038-5", "papers/cmaa.pdf"] {
    guard links.contains(where: { $0.absoluteString.contains(needle) }) else {
        fatalError("Missing reference/source link: \(needle)")
    }
}

let totalWords = bodyText.replacingOccurrences(of: "-\n", with: "")
    .split(whereSeparator: { $0.isWhitespace }).joined(separator: " ")
guard totalWords.contains("not yet formalized"),
      totalWords.contains("code-to-code computation"),
      totalWords.contains("not a checked cross-language"),
      totalWords.contains("internal reflection") else {
    fatalError("Missing compilation/consistency scope boundaries")
}

for needle in ["Total typed apply-and-normalize", "Graded fragment soundness",
               "The executable interface is total", "output-typed", "normal-result",
               "no normalization or output-typing certificate is an input",
               "exact original output typing", "subject reduction",
               "idempotent", "independent of the sufficient rank budget",
               "bounded trace", "beta-convertible exactly when",
               "injective embeddings satisfying identity and composition",
               "arbitrary well-typed syntactic substitutions",
               "all-six-rule contextual soundness",
               "finite first-order model of a logical fragment",
               "Operations that increase grades do not automatically supply this closure",
               "Every typed valuation between well-formed contexts",
               "no native typing, well-formedness or normalization premise is hidden",
               "Acceptance implies original Typ",
               "no guessed budget or desired output",
               "only for rejected certificates",
               "Agda metatheorems, not internal PTS consistency proofs"] {
    guard totalWords.contains(needle) else {
        fatalError("Missing totality/model-soundness content: \(needle)")
    }
}
for stale in ["not yet the total typed interface",
              "rank lemma remain to be proved in Agda",
              "prove the Agda typed-totality obligation",
              "Executable application and the typed-totality boundary"] {
    guard !totalWords.contains(stale) else {
        fatalError("Stale totality claim: \(stale)")
    }
}

for needle in ["including every alleged proof of Void", "add the denials",
               "every model, not merely the chosen least one",
               "empty ground Void fibre", "Consistency-sensitive ground reduction",
               "no forbidden list is jointly derivable", "singleton domain carries no syntax",
               "does not mean that these predicates are all true",
               "Original-PTS-to-catalogue completeness remains unformalized",
               "Literal MM0 adequacy and finite models",
               "No consistency or model existence premise remains",
               "every finite list of valid catalogue-rule instances",
               "including subjects outside the observed atom set",
               "relative to", "need not survive adding more source rules",
               "not a claim that underivability entails negation",
               "Saturation and table generation here occur externally",
               "not a uniform internal saturation algorithm",
               "does not apply to typed or resource-indexed application",
               "predicate, which is not equality",
               "Enumerate all vectors", "under every valuation",
               "same fixed", "not an existence theorem for every fragment",
               "actual finite diagram"] {
    guard totalWords.contains(needle) else {
        fatalError("Missing constrained-model scope/content: \(needle)")
    }
}
for needle in ["The finite native-model boundary", "Consequently the domain is infinite",
               "Total constructor search and internal certificates",
               "all 55 named universal axioms", "Selection retains whole axioms",
               "equal sort cardinalities", "omitting", "disables positive catalogue introduction",
               "finite continuation conjunction", "rank at most four",
               "not a kernel-verified MM0 parser", "source derivations",
               "not an existence theorem for every fragment"] {
    guard totalWords.contains(needle) else {
        fatalError("Missing quantified-model scope/content: \(needle)")
    }
}
for stale in ["make every", "all-true Horn models", "all-true ground-Horn reduction"] {
    guard !totalWords.contains(stale) else {
        fatalError("Stale positive-only consistency argument: \(stale)")
    }
}

guard let futureStart = bodyText.range(of: "Future work"),
      let futureEnd = bodyText.range(of: "References",
          range: futureStart.upperBound..<bodyText.endIndex) else {
    fatalError("Missing bounded future-work section")
}
let futureText = String(bodyText[futureStart.upperBound..<futureEnd.lowerBound])
let futureWords = futureText.replacingOccurrences(of: "-\n", with: "")
    .split(whereSeparator: { $0.isWhitespace }).joined(separator: " ")
for needle in ["1. A quadratically checkable PTS-rk variant.",
               "2. A logic-free arithmetic of partial functions.",
               "3. Interpretation of the type theory in the arithmetic.",
               "proposed systems", "propositional computation and transport witnesses",
               "numerical ranks", "all annotations and witnesses",
               "Terms denote partial functions", "extension, not equality",
               "graph of", "symmetry is not an inference rule",
               "Every partial computable function", "term-forming basis",
               "reflexivity, transitivity and substitution", "induction rule",
               "finite core of axioms", "exists", "either all numbers are equal",
               "initial segment of at least", "distinct natural numbers",
               "local finite satisfiability", "finite model validating the inference rules",
               "Noncollapsed finite models", "collapse disjunct",
               "derivation checking", "full encoded derivation length",
               "induction certificates", "inside the system in (2)",
               "computation witnesses and contradiction"] {
    guard futureWords.contains(needle) else {
        fatalError("Missing future-work requirement: \(needle)")
    }
}

try text.write(toFile: out + "/pdf-text.txt", atomically: true, encoding: .utf8)
try links.map { $0.absoluteString }.joined(separator: "\n").write(
    toFile: out + "/pdf-links.txt", atomically: true, encoding: .utf8)
for index in 0..<doc.pageCount {
    let page = pages[index]
    let bounds = page.bounds(for: .mediaBox)
    let img = page.thumbnail(of: NSSize(width: bounds.width * 1.25, height: bounds.height * 1.25), for: .mediaBox)
    guard let data = img.tiffRepresentation, let bitmap = NSBitmapImageRep(data: data),
          let png = bitmap.representation(using: .png, properties: [:]) else {
        fatalError("Page rendering failed")
    }
    try png.write(to: URL(fileURLWithPath: out + "/page-\(index + 1).png"))
}
let futurePages = pages.enumerated().compactMap { index, page in
    let pageText = page.string ?? ""
    return pageText.contains("Future work") ||
        pageText.contains("A quadratically checkable PTS-rk variant") ||
        pageText.contains("Interpretation of the type theory in the arithmetic") ? index + 1 : nil
}
let changedPages = pages.enumerated().compactMap { index, page in
    let pageText = page.string ?? ""
    return pageText.contains("Total typed apply-and-normalize") ||
        pageText.contains("Graded fragment soundness") ||
        pageText.contains("NativeNormalization") ||
        pageText.contains("FragmentApplication") ||
        pageText.contains("applyTypedWithin") ||
        pageText.contains("Contextual certificate soundness") ||
        pageText.contains("model-soundness") ||
        pageText.contains("FragmentPackages") ||
        pageText.contains("NativeCanonicity") ||
        pageText.contains("finite first-order model") ||
        pageText.contains("type carrier cannot") ||
        pageText.contains("Consistency-sensitive ground reduction") ||
        pageText.contains("Exact finite ground fragments") ||
        pageText.contains("signed diagram") ||
        pageText.contains("query_program") ||
        pageText.contains("FiniteModelBoundary") ||
        pageText.contains("check_candidate") ||
        pageText.contains("size/depth-guarded") ||
        pageText.contains("Proof height is a separate parameter") ||
        pageText.contains("Reduction witnesses can also") ||
        pageText.contains("literal MM0 syntax") ||
        pageText.contains("Literal MM0 adequacy") ||
        pageText.contains("Consistent finite models") ||
        pageText.contains("MM0CatalogueRealization") ? index + 1 : nil
}
print("Changed-content pages: \(changedPages)")
print("PASS: pages=\(doc.pageCount), appendix=\(doc.pageCount - appendix) pages, source badges=\(sourceLinks.count), Agda badges=\(agdaBadges.count), Agda links=\(agdaLinks.count), links=\(links.count), future-work pages=\(futurePages)")
