import { addDecorator, configure } from '@storybook/react'
import { ThemeProvider, createGlobalStyle } from 'styled-components'
import React from 'react'
import { Router } from 'react-router-dom'
import { createBrowserHistory } from 'history'
import { normalize } from 'polished'
import { defaultTheme } from '../src/defaultTheme'

const history = createBrowserHistory()

const GlobalStyle = createGlobalStyle`
${normalize()}
`

addDecorator((story) => {
  // console.log('defaultTheme', defaultTheme)
  return (
    <ThemeProvider theme={defaultTheme}>
      <GlobalStyle />
      <Router history={history}>{story()}</Router>
    </ThemeProvider>
  )
})

export const parameters = {
  actions: { argTypesRegex: '^on.*' },
}
