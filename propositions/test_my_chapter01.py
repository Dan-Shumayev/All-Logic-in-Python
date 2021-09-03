# this test file will test all chapter-1's related functionalities

from propositions.syntax import *


def test_parse():
    assert parse("Test to be taken!")
