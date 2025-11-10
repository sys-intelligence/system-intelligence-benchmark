from src.sdk import Evaluator


def test_jaccard_similarity_ngrams():
    evaluator = Evaluator()
    result = evaluator.jaccard_similarity_ngrams('hello world', 'hello')
    assert result == 0.4, f'Expected 0.4, got {result}'


def test_syntax_correctness():
    evaluator = Evaluator()
    result = evaluator.syntax_correctness(
        'cluster("azcore.centralus").database("AzureCP").MycroftNodeHealthSnapshot\n| where PreciseTimeStamp  >= ago(1d)'
    )
    assert result == 1, f'Expected 1, got {result}'


def test_exact_match():
    evaluator = Evaluator()
    result = evaluator.exact_match('hello', 'hello')
    assert result == 1, f'Expected 1, got {result}'
