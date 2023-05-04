import json
from pathlib import Path

class CoverageResult:
    def __init__(self):
        self.info = {}

    def add_file(self,path,name,obj):
        target_path = path / name
        self.info[str(target_path)] = obj

    def show_result(self):
        results = []
        for filename in self.info.keys():
            file_result_dict = {"name":filename}
            for key in ['coveragePercent','linesCovered','linesMissed']:
                file_result_dict[key] = self.info[filename][key]

            results.append(file_result_dict)

        return results

def distill_coverage(result,path,container):
    if not 'children' in container:
        nice_cov_dict = {}
        for item in ['coveragePercent','linesCovered','linesMissed']:
            nice_cov_dict[item] = container[item]
        result.add_file(path, path, nice_cov_dict)
        return

    for subpath in container['children'].keys():
        distill_coverage(result, path / subpath, container['children'][subpath])

if __name__ == '__main__':
    import argparse

    parser = argparse.ArgumentParser()
    parser.add_argument('covfile')
    args = parser.parse_args()

    result = CoverageResult()
    infile = json.loads(open(args.covfile).read())
    for root in infile['children'].keys():
        distill_coverage(result, Path(root), infile['children'][root])

    print(json.dumps(result.show_result(), indent=4))
