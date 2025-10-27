# Release Process

## Quick Steps

1. Update version in `build.gradle.kts`
2. Update `CHANGELOG.md` with release notes
3. Commit: `git commit -m "Prepare vX.Y.Z release"`
4. Push to main and wait for CI to pass
5. Create and push tag:
   ```bash
   git tag vX.Y.Z
   git push origin vX.Y.Z
   ```
6. GitHub Actions will automatically create the release

## Workflow

- Triggers on tags matching `v*.*.*`
- Builds fat JAR with `./gradlew buildFatJar`
- Creates release with JAR and auto-generated notes
- **Note:** Only tag commits on main that already passed CI

## Troubleshooting

**Delete a tag:**
```bash
git tag -d vX.Y.Z
git push origin :refs/tags/vX.Y.Z
```

**Manual release:**
```bash
./gradlew clean buildFatJar
# Upload build/libs/tlaplus-formatter.jar to GitHub Releases manually
```
