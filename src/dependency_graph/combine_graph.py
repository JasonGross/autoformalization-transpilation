import os
import re
from typing import Dict, Tuple, List

dpdDir: str = "/root/lf/dgraph"
outputFile: str = os.path.join(dpdDir, "dgraph.dpd")

nodeMap: Dict[str, Tuple[int, str]] = {}
nextGlobalId: int = 1
edges: List[Tuple[int, int, str]] = []

def processDpdFile(filePath: str) -> List[Tuple[int, int, str]]:
    global nextGlobalId

    localMap: Dict[int, int] = {}
    fileEdges: List[Tuple[int, int, str]] = []

    with open(filePath, "r", encoding="utf-8") as dpdFile:
        for line in dpdFile:
            nodeMatch = re.match(r'N: (\d+) "(.*?)" (\[.*?\])?;', line)
            edgeMatch = re.match(r'E: (\d+) (\d+) (\[.*?\])?;', line)

            if nodeMatch:
                oldId: int = int(nodeMatch.group(1))
                nodeName: str = nodeMatch.group(2)
                attributes: str = nodeMatch.group(3) if nodeMatch.group(3) else ""

                if nodeName not in nodeMap:
                    nodeMap[nodeName] = (nextGlobalId, attributes)
                    nextGlobalId += 1

                localMap[oldId] = nodeMap[nodeName][0]

            elif edgeMatch:
                oldSrc: int = int(edgeMatch.group(1))
                oldDst: int = int(edgeMatch.group(2))
                edgeAttributes: str = edgeMatch.group(3) if edgeMatch.group(3) else ""
                fileEdges.append((oldSrc, oldDst, edgeAttributes))

    updatedEdges: List[Tuple[int, int, str]] = [
        (localMap[src], localMap[dst], attr) for src, dst, attr in fileEdges
    ]
    return updatedEdges

allFiles: List[str] = [file for file in os.listdir(dpdDir) if file.endswith(".dpd")]
finalEdges: List[Tuple[int, int, str]] = []

for dpdFile in allFiles:
    filePath: str = os.path.join(dpdDir, dpdFile)
    finalEdges.extend(processDpdFile(filePath))

with open(outputFile, "w", encoding="utf-8") as mergedFile:
    for nodeName, (globalId, attributes) in nodeMap.items():
        mergedFile.write(f'N: {globalId} "{nodeName}" {attributes};\n')

    for src, dst, attr in finalEdges:
        mergedFile.write(f"E: {src} {dst} {attr};\n")

print(f"Dependency graphs merged successfully into {outputFile}")
