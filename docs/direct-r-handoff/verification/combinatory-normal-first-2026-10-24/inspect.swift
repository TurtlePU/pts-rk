import Foundation
import AppKit
import PDFKit

let pdfPath = CommandLine.arguments[1]
let output = CommandLine.arguments[2]
let source = URL(fileURLWithPath: pdfPath).deletingLastPathComponent()
guard let document = PDFDocument(url: URL(fileURLWithPath: pdfPath)) else {
    fatalError("Unreadable PDF")
}
let pages = (0..<document.pageCount).map { document.page(at: $0)! }
let text = pages.map { $0.string ?? "" }.joined(separator: "\n")
let words = text.replacingOccurrences(of: "-\n", with: "")
    .split(whereSeparator: { $0.isWhitespace }).joined(separator: " ")
let links = pages.flatMap { page in
    page.annotations.compactMap { annotation in
        annotation.url ?? (annotation.action as? PDFActionRemoteGoTo)?.url
    }
}
try text.write(toFile: output + "/pdf-text.txt", atomically: true, encoding: .utf8)
try links.map { $0.absoluteString }.joined(separator: "\n").write(
    toFile: output + "/pdf-links.txt", atomically: true, encoding: .utf8)

for required in ["The rank-typed SK interface", "Typed SK compilation",
                 "Binder-free normalization and bidirectional checking",
                 "Canonical beta representatives", "apply-sound", "idempotent",
                 "check-canonical", "quotient-normal-iso", "coherent", "reflects",
                 "Direct evaluation and its canonical-image boundary",
                 "A normal-form-first algebra", "computed-type fibre",
                 "normal images", "associativity paths", "syntax-only budget",
                 "The exact PTS boundary", "The literal catalogue and its completeness boundary",
                 "Elementary normalization and finite syntax carriers",
                 "Total typed apply-and-normalize", "Internal decoding and guarded computation"] {
    guard words.contains(required) else { fatalError("Missing content: \(required)") }
}
guard !words.contains("BCKW") else { fatalError("Superseded basis remains in paper") }
guard let appendix = pages.firstIndex(where: {
    ($0.string ?? "").contains("Complete MM0 source")
}), (1...3).contains(pages.count - appendix) else {
    fatalError("MM0 appendix missing or exceeds three pages")
}
guard pages[appendix...].map({ $0.string ?? "" }).joined().contains("ENDHILBERT") else {
    fatalError("Incomplete MM0 appendix")
}
let rocq = links.filter { $0.pathExtension == "v" }
let agda = links.filter { $0.pathExtension == "agda" }
guard rocq.count == 72 else { fatalError("Expected 72 Rocq proof links") }
for link in rocq + agda {
    let path = (link.pathExtension == "agda" ? "agda/" : "") + link.lastPathComponent
    guard FileManager.default.fileExists(atPath: source.appendingPathComponent(path).path) else {
        fatalError("Proof source missing: \(path)")
    }
}
let badges = pages.flatMap { page in
    page.annotations.filter { annotation in
        let url = annotation.url ?? (annotation.action as? PDFActionRemoteGoTo)?.url
        return url?.pathExtension == "agda" &&
            (page.selection(for: annotation.bounds)?.string ?? "").contains("agda (proof)")
    }
}
guard badges.count == 48 else { fatalError("Expected all 48 Agda proof badges") }
for name in ["BinderFreeCore", "BinderFreeBidirectional", "BinderFreeCoherence",
             "BinderFreeEquality", "BinderFreeQuotient", "BinderFreeBoundary",
             "SKNativeCanonical", "SKSource", "SKSourceEquality", "SKSourceNormal",
             "SKBracket", "SKCanonicalNormal", "SKCanonical", "SKSourceRank",
             "SKCanonicalExamples", "SKDirectSoundness", "SKDirectGround",
             "SKDirectBoundary", "CanonicalAlgebra", "NormalizedSubstitution",
             "SKBracketSize"] {
    guard agda.contains(where: { $0.lastPathComponent == name + ".agda" }) else {
        fatalError("Missing formalization link: \(name)")
    }
}
for (index, page) in pages.enumerated() {
    let bounds = page.bounds(for: .mediaBox)
    let image = page.thumbnail(of: bounds.size, for: .mediaBox)
    guard let data = image.tiffRepresentation,
          let bitmap = NSBitmapImageRep(data: data),
          let png = bitmap.representation(using: .png, properties: [:]) else {
        fatalError("Page rendering failed")
    }
    try png.write(to: URL(fileURLWithPath: output + "/page-\(index + 1).png"))
    let pageText = page.string ?? ""
    if ["Canonical beta representatives", "syntax-only budget", "SKSource",
        "apply-sound", "Direct evaluation", "canonical-image closure",
        "normal-form-first", "computed-type fibre", "normal images",
        "associativity paths", "compiler", "4^(tower"].contains(where: pageText.contains) {
        print("Review changed page \(index + 1)")
    }
}
print("PASS: \(pages.count) pages; appendix \(pages.count - appendix); " +
      "\(rocq.count) Rocq / \(badges.count) Agda badges; \(links.count) links")
